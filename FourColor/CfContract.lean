import FourColor.CfColor

/-!
# The contract of a configuration

A configuration is reducible because contracting a small set of its edges
produces a map whose colourings, pulled back, cover the ring colourings of the
configuration up to Kempe flips.  This module computes that contract from the
configuration data and checks its validity.

Contracts are represented, as in `FourColor.Coloring`, by a transversal of the
contracted edges.  The configuration record stores them as a list of *indices*
into a transversal of the kernel edges of the constructed map, listed in the
reverse order in which they become kernel edges during the construction: each
`Y` step contributes its foot (except the initial `Y`, after which every edge is
still a ring edge), and each `H` step contributes its crossbar and then its left
and right feet.  Out-of-range indices are ignored, so a contract never meets the
ring.

## Main definitions

* `ctrmsize`, `ctrenum` — the number of kernel edges of `cpmap cp`, and a
  transversal of them.
* `ctrmaskRec`, `ctrmask` — the bit mask of a list of contract indices.
* `cfctr` — the construction program of the contracted map: `cfctr cp mr mc`
  erases the kernel edges selected by `mc` and the ring edges selected by `mr`
  (the latter only arise in recursive calls), and returns `none` when the
  contract is not sparse or `cp` is not a configuration program.
* `ctrband` — the `CfMask` selecting the faces incident to a contract edge.
* `cptriad`, `validCtrm` — the validity check on a contract mask: one to four
  edges, and a triad when there are four.
* `cfcontractMask`, `cfcontract`, `contractCtree` — the contract of a
  configuration, and the tree of its contract colourings.

## Main results

* `length_ctrmask`, `length_ctrenum` — both the mask and the transversal have
  `ctrmsize cp` entries, so they match up.
* `insertE_map` and `insertE_injcpStep` — the edge closure commutes with any
  injection commuting with `edge`, in particular with the dart injections of a
  construction step.
* `ConfigProg.of_cfctr` — `cfctr` only succeeds on configuration programs; this
  is what turns the dynamic check into a proof.
* `cprsize_cfctr` — the contracted map has one ring dart per ring dart *not*
  erased by `mr`.
* `properCfMask_ctrband` — `ctrband` returns a proper mask.
* `count_pos_of_validCtrm`, `count_le_four_of_validCtrm`, `length_cfcontract`,
  `one_le_length_cfcontract`, `length_cfcontract_le_four` — a valid contract has
  between one and four edges.
* `exists_cfctr_of_contractCtree`, `ConfigProg.of_contractCtree` — what a
  successful contract computation says about the configuration.
* `uniq_ctrenum` — **the kernel edge transversal really is a transversal**: the
  ring and `ctrenum`, closed under `edge`, list pairwise distinct darts.  Every
  semantic result about contracts rests on this.
* `notMem_cfring_of_mem_insertE_cfcontract` — a contract never meets the ring;
  this is the `off_ring` half of `Hypermap.ValidContract`.
* `ctrband_correct` — **`ctrband` computes the band of a contract**: its mask
  selects exactly the faces met by the edge closure of the contract.

* `CfctrSpec` — the specification of `cfctr`: a contract colouring of `cpmap cp`
  for the contract selected by `mr` and `mc` restricts to a colouring of the
  contracted map whose ring trace is the trace of the ring darts `mr` keeps.
* `extColoring`, `coloring_extColoring` — extending a colouring of the map below
  along a construction step, and the criterion for the result to be a colouring;
  `head_listMask_not` — the colour of the ring is constant along a contracted
  stretch.
* `cfctrSpec_R`, `cfctrSpec_Y_nil`, `cfctrSpec_Y_erase`, `cfctrSpec_Y_U`,
  `cfctrSpec_Y_Y`, `cfctrSpec_H_crossbar`, `cfctrSpec_H_erase1`,
  `cfctrSpec_H_erase2`, `cfctrSpec_H_U`, `cfctrSpec_H_Y`, `cfctrSpec_H_H`,
  `cfctrSpec_H_K`, `cfctrSpec_H_A` — the fourteen step cases of
  `cfctr_correct`.
* `walk_headD`, `contracted_ring_head` — walking around the ring of a contract
  colouring: when the contract erases every ring edge after the reference dart
  the walk wraps around the ring, which is what the `K` and `A` cases need.
* `cfctr_correct` — **`cfctr` is correct**: it assembles from the fourteen step
  cases by the case tree of `cfctr` itself.

* `ctrList`, `sparse_cfctr` — the list whose node-simplicity `cfctr` checks —
  the E-partners of the ring darts the ring mask selects together with the edge
  closure of the kernel darts the kernel mask selects — and the proof that
  `cfctr` only accepts node-simple contracts.
* `triad_of_cptriad` — a kernel face that `cptriad` accepts really is a triad
  for the contract.
* `contract_ctreeP` — **the contract of a configuration is valid, and its
  contract colourings are in the tree**: the last ingredient of the
  reducibility check.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file
corresponds to `theories/proof/cfcontract.v` of the Coq development.
-/

namespace FourColor

/-! ### The kernel edges of a configuration map -/

/-- The number of kernel (non-ring) edges of `cpmap cp`.  Every `Y` step but the
last one executed — that is, the last one of the program, since programs run
right to left — contributes its foot, and every `H` step contributes three
edges. -/
def ctrmsize : CProg → ℕ
  | .R _ :: cp => ctrmsize cp
  | .Y :: [] => 0
  | .Y :: s :: cp => ctrmsize (s :: cp) + 1
  | .H :: cp => ctrmsize cp + 3
  | _ => 0

@[simp] theorem ctrmsize_nil : ctrmsize [] = 0 := rfl

@[simp] theorem ctrmsize_R (n : ℕ) (cp : CProg) : ctrmsize (.R n :: cp) = ctrmsize cp := rfl

@[simp] theorem ctrmsize_Y_nil : ctrmsize [.Y] = 0 := rfl

@[simp] theorem ctrmsize_Y_cons (s : CpStep) (cp : CProg) :
    ctrmsize (.Y :: s :: cp) = ctrmsize (s :: cp) + 1 := rfl

@[simp] theorem ctrmsize_H (cp : CProg) : ctrmsize (.H :: cp) = ctrmsize cp + 3 := rfl

/-- A transversal of the kernel edges of `cpmap cp`, in the reverse order in
which the edges become kernel edges: the foot of each `Y` step (except the
initial one, at the end of the program), and the crossbar and then the two feet
of each `H` step. -/
noncomputable def ctrenum : (cp : CProg) → List (cpmap cp).Dart
  | .R _ :: cp => ctrenum cp
  | .Y :: [] => []
  | .Y :: s :: cp =>
      ((cpmap (s :: cp)).map.node (cpmap (s :: cp)).point :: ctrenum (s :: cp)).map
        (injcpStep .Y (s :: cp))
  | .H :: cp =>
      (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point ::
        ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: ctrenum cp).map
          (injcpStep .H cp)
  | [] => []
  | .R' :: _ => []
  | .U :: _ => []
  | .K :: _ => []
  | .A :: _ => []

@[simp] theorem ctrenum_nil : ctrenum [] = [] := rfl

@[simp] theorem ctrenum_R (n : ℕ) (cp : CProg) : ctrenum (.R n :: cp) = ctrenum cp := rfl

@[simp] theorem ctrenum_Y_nil : ctrenum [.Y] = [] := rfl

@[simp] theorem ctrenum_Y_cons (s : CpStep) (cp : CProg) :
    ctrenum (.Y :: s :: cp)
      = ((cpmap (s :: cp)).map.node (cpmap (s :: cp)).point :: ctrenum (s :: cp)).map
          (injcpStep .Y (s :: cp)) := rfl

@[simp] theorem ctrenum_H (cp : CProg) :
    ctrenum (.H :: cp)
      = (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point ::
          ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: ctrenum cp).map
            (injcpStep .H cp) := rfl

/-- The transversal of the kernel edges has the predicted length. -/
theorem length_ctrenum : ∀ cp : CProg, (ctrenum cp).length = ctrmsize cp := by
  intro cp
  induction cp with
  | nil => rfl
  | cons s cp ih =>
    cases s with
    | R n => exact ih
    | R' => rfl
    | Y => cases cp with
      | nil => rfl
      | cons t cp =>
        simp only [ctrenum_Y_cons, ctrmsize_Y_cons, List.length_map, List.length_cons, ih]
    | H =>
      simp only [ctrenum_H, ctrmsize_H, List.length_map, List.length_cons, ih]
    | U => rfl
    | K => rfl
    | A => rfl

/-! ### Contract masks -/

/-- The bit mask of the contract index list `cci` for `n` edges starting at
index `i`. -/
def ctrmaskRec (cci : List ℕ) (i : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => decide (i ∈ cci) :: ctrmaskRec cci (i + 1) n

@[simp] theorem length_ctrmaskRec (cci : List ℕ) (i n : ℕ) :
    (ctrmaskRec cci i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [ctrmaskRec, ih]

/-- The bit mask selecting the kernel edges of `cpmap cp` whose index occurs in
the contract index list `cci`.  Out-of-range indices are ignored. -/
def ctrmask (cp : CProg) (cci : List ℕ) : List Bool := ctrmaskRec cci 0 (ctrmsize cp)

@[simp] theorem length_ctrmask (cp : CProg) (cci : List ℕ) :
    (ctrmask cp cci).length = ctrmsize cp := length_ctrmaskRec _ _ _

/-! ### The edge closure and dart injections -/

/-- The edge closure commutes with any map commuting with `edge`. -/
theorem insertE_map {D D' : Type*} (G : Hypermap D) (G' : Hypermap D') (f : D → D')
    (hf : ∀ x, f (G.edge x) = G'.edge (f x)) (p : List D) :
    G'.insertE (p.map f) = (G.insertE p).map f := by
  induction p with
  | nil => rfl
  | cons x p ih => simp [Hypermap.insertE, ih, hf x]

/-- The edge closure commutes with the dart injection of a construction step. -/
theorem insertE_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg)
    (p : List (cpmap cp).Dart) :
    (cpmap (s :: cp)).map.insertE (p.map (injcpStep s cp))
      = ((cpmap cp).map.insertE p).map (injcpStep s cp) :=
  insertE_map _ _ _ (edge_injcpStep hs cp) p

/-- Every dart of a list lies in its edge closure. -/
theorem mem_insertE_self {D : Type*} (G : Hypermap D) : ∀ {p : List D} {x : D},
    x ∈ p → x ∈ G.insertE p := by
  intro p
  induction p with
  | nil => intro x hx; cases hx
  | cons y p ih =>
    intro x hx
    cases hx with
    | head => exact List.Mem.head _
    | tail _ hx => exact List.Mem.tail _ (List.Mem.tail _ (ih hx))

/-- The edge partner of a dart of a list lies in its edge closure. -/
theorem mem_insertE_edge {D : Type*} (G : Hypermap D) : ∀ {p : List D} {x : D},
    x ∈ p → G.edge x ∈ G.insertE p := by
  intro p
  induction p with
  | nil => intro x hx; cases hx
  | cons y p ih =>
    intro x hx
    cases hx with
    | head => exact List.Mem.tail _ (List.Mem.head _)
    | tail _ hx => exact List.Mem.tail _ (List.Mem.tail _ (ih hx))

/-- The edge closure is monotone. -/
theorem insertE_mono {D : Type*} (G : Hypermap D) : ∀ {p q : List D}, (∀ y ∈ p, y ∈ q) →
    ∀ {x : D}, x ∈ G.insertE p → x ∈ G.insertE q := by
  intro p
  induction p with
  | nil => intro q _ x hx; cases hx
  | cons y p ih =>
    intro q h x hx
    have hy : y ∈ q := h y (List.Mem.head _)
    cases hx with
    | head => exact mem_insertE_self G hy
    | tail _ hx =>
      cases hx with
      | head => exact mem_insertE_edge G hy
      | tail _ hx => exact ih (fun z hz => h z (List.Mem.tail _ hz)) hx

/-- Permuting a list permutes its edge closure. -/
theorem insertE_perm {D : Type*} (G : Hypermap D) {p q : List D} (h : p.Perm q) :
    (G.insertE p).Perm (G.insertE q) := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons x _ ih => exact (ih.cons (G.edge x)).cons x
  | swap x y l =>
    exact (List.perm_append_comm.append_right (G.insertE l) :
      (([y, G.edge y] ++ [x, G.edge x]) ++ G.insertE l).Perm
        (([x, G.edge x] ++ [y, G.edge y]) ++ G.insertE l))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Moving the third block of a fourfold concatenation next to the first. -/
private theorem perm_append_move {α : Type*} (l₁ l₂ l₃ l₄ : List α) :
    (l₁ ++ (l₂ ++ (l₃ ++ l₄))).Perm ((l₁ ++ l₃) ++ (l₂ ++ l₄)) := by
  have h : (l₂ ++ (l₃ ++ l₄)).Perm (l₃ ++ (l₂ ++ l₄)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  rw [List.append_assoc]
  exact h.append_left l₁

/-- The four darts of the two new edges of a `Y` step are distinct. -/
private theorem nodup_new_ecpY (M : PointedMap) :
    (([EcpDart.icp EcpDart.Xe, EcpDart.icp EcpDart.X,
      EcpDart.X, EcpDart.Xe] : List M.ecpY.Dart)).Nodup := by
  change (([EcpDart.icp EcpDart.Xe, EcpDart.icp EcpDart.X,
      EcpDart.X, EcpDart.Xe] : List (EcpDart (EcpDart M.Dart)))).Nodup
  simp

/-- No old dart of a `Y` step is one of the four new darts. -/
private theorem icpY_notMem_new (M : PointedMap) (x : M.Dart) :
    M.icpY x ∉ ([EcpDart.icp EcpDart.Xe, EcpDart.icp EcpDart.X,
      EcpDart.X, EcpDart.Xe] : List M.ecpY.Dart) := by
  change (EcpDart.icp (EcpDart.icp x) : EcpDart (EcpDart M.Dart))
    ∉ ([EcpDart.icp EcpDart.Xe, EcpDart.icp EcpDart.X,
      EcpDart.X, EcpDart.Xe] : List (EcpDart (EcpDart M.Dart)))
  simp

/-- The six darts of the three new edges of an `H` step are distinct. -/
private theorem nodup_new_ecpH (M : PointedMap) :
    (([EcpDart.icp (EcpDart.icp EcpDart.Xe),
      EcpDart.icp (EcpDart.icp EcpDart.X), EcpDart.X, EcpDart.Xe,
      EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] : List M.ecpH.Dart)).Nodup := by
  change (([EcpDart.icp (EcpDart.icp EcpDart.Xe),
      EcpDart.icp (EcpDart.icp EcpDart.X), EcpDart.X, EcpDart.Xe,
      EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] :
        List (EcpDart (EcpDart (EcpDart M.Dart))))).Nodup
  simp

/-- No old dart of an `H` step is one of the six new darts. -/
private theorem icpH_notMem_new (M : PointedMap) (x : M.Dart) :
    M.icpH x ∉ ([EcpDart.icp (EcpDart.icp EcpDart.Xe),
      EcpDart.icp (EcpDart.icp EcpDart.X), EcpDart.X, EcpDart.Xe,
      EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] : List M.ecpH.Dart) := by
  change (EcpDart.icp (EcpDart.icp (EcpDart.icp x)) : EcpDart (EcpDart (EcpDart M.Dart)))
    ∉ ([EcpDart.icp (EcpDart.icp EcpDart.Xe),
      EcpDart.icp (EcpDart.icp EcpDart.X), EcpDart.X, EcpDart.Xe,
      EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] :
        List (EcpDart (EcpDart (EcpDart M.Dart))))
  simp

/-- **The `Y` step of the transversal lemma.**  A `Y` step adds two new edges at
the top of its ring; their four darts are new, so the edge closure of the ring
together with the kernel transversal stays duplicate-free. -/
private theorem nodup_insertE_ecpY (M : PointedMap) {L : List M.Dart}
    (hL : (M.map.insertE L).Nodup) :
    (M.ecpY.map.insertE
        (M.ecpY.map.node M.ecpY.point :: M.ecpY.point :: L.map M.icpY)).Nodup := by
  have hnode : M.ecpY.map.node M.ecpY.point = (EcpDart.icp EcpDart.Xe : M.ecpY.Dart) :=
    PointedMap.node_ecpY M
  have hkey : M.ecpY.map.insertE
        (M.ecpY.map.node M.ecpY.point :: M.ecpY.point :: L.map M.icpY)
      = ([EcpDart.icp EcpDart.Xe, EcpDart.icp EcpDart.X,
          EcpDart.X, EcpDart.Xe] : List M.ecpY.Dart) ++ (M.map.insertE L).map M.icpY := by
    rw [Hypermap.insertE_cons, Hypermap.insertE_cons,
      insertE_map M.map M.ecpY.map M.icpY (fun _ => rfl) L, hnode]
    rfl
  rw [hkey]
  refine List.nodup_append.mpr
    ⟨nodup_new_ecpY M, hL.map (PointedMap.icpY_injective M), ?_⟩
  intro u hu v hv
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
  exact fun hc => icpY_notMem_new M x (hc ▸ hu)

/-- **The `H` step of the transversal lemma.**  An `H` step adds its two new ring
edges and its crossbar; all six darts are new, so the edge closure of the ring
together with the kernel transversal stays duplicate-free. -/
private theorem nodup_insertE_ecpH (M : PointedMap) (hp : M.Proper) {A B : List M.Dart}
    (hL : (M.map.insertE (A ++ B)).Nodup) :
    (M.ecpH.map.insertE
        (M.ecpH.map.node M.ecpH.point :: M.ecpH.point
          :: (A.map M.icpH
              ++ M.ecpH.map.face M.ecpH.point :: B.map M.icpH))).Nodup := by
  have hmap : ((M.map.insertE A).map M.icpH ++ (M.map.insertE B).map M.icpH).Nodup := by
    rw [← List.map_append, ← Hypermap.insertE_append]
    exact hL.map (PointedMap.icpH_injective M)
  have hnode : M.ecpH.map.node M.ecpH.point
      = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : M.ecpH.Dart) := PointedMap.node_ecpH M hp
  have hkey : M.ecpH.map.insertE
        (M.ecpH.map.node M.ecpH.point :: M.ecpH.point
          :: (A.map M.icpH ++ M.ecpH.map.face M.ecpH.point :: B.map M.icpH))
      = ([EcpDart.icp (EcpDart.icp EcpDart.Xe),
          EcpDart.icp (EcpDart.icp EcpDart.X), EcpDart.X, EcpDart.Xe] : List M.ecpH.Dart)
        ++ ((M.map.insertE A).map M.icpH
            ++ (([EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] : List M.ecpH.Dart)
                ++ (M.map.insertE B).map M.icpH)) := by
    rw [Hypermap.insertE_cons, Hypermap.insertE_cons, Hypermap.insertE_append,
      Hypermap.insertE_cons,
      insertE_map M.map M.ecpH.map M.icpH (fun _ => rfl) A,
      insertE_map M.map M.ecpH.map M.icpH (fun _ => rfl) B, hnode]
    rfl
  rw [hkey]
  refine (perm_append_move _ _ _ _).nodup_iff.mpr ?_
  refine List.nodup_append.mpr ⟨nodup_new_ecpH M, hmap, ?_⟩
  intro u hu v hv
  rcases List.mem_append.mp hv with hv | hv <;>
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
      exact fun hc => icpH_notMem_new M x (hc ▸ hu)

/-- **The kernel edge transversal really is a transversal.**  The ring of a
configuration map together with `ctrenum`, closed under `edge`, is a list of
pairwise distinct darts: `ctrenum` meets each kernel edge exactly once, and
never meets the ring. -/
theorem uniq_ctrenum : ∀ {cp : CProg}, ConfigProg cp →
    ((cpmap cp).map.insertE ((cpmap cp).cpring ++ ctrenum cp)).Nodup := by
  intro cp
  induction cp with
  | nil => intro h; exact absurd h.2 (by simp)
  | cons s cp ih =>
    intro h
    have hs := h.1 s List.mem_cons_self
    cases s with
    | R' => exact hs.elim
    | U => exact hs.elim
    | K => exact hs.elim
    | A => exact hs.elim
    | R n =>
      have hnil : cp ≠ [] := by rintro rfl; exact absurd h.2 (by simp)
      have hih := ih (h.of_cons hnil)
      have hr : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
        Hypermap.cpring_ecpR (G := (cpmap cp).map) (x₀ := (cpmap cp).point) n
      have hperm : ((cpmap cp).cpring.rotate n ++ ctrenum cp).Perm
          ((cpmap cp).cpring ++ ctrenum cp) := (List.rotate_perm _ n).append_right _
      rw [ctrenum_R, hr]
      exact (insertE_perm (cpmap cp).map hperm).nodup_iff.mpr hih
    | Y =>
      cases cp with
      | nil =>
        have hbase :
            ((cpmap ([] : CProg)).map.insertE (cpmap ([] : CProg)).cpring.tail).Nodup := by
          have h2 : (cpmap ([] : CProg)).cpring.tail.length = 1 := by
            have h0 : (cpmap ([] : CProg)).cpring.length = 2 :=
              PointedMap.length_cpring_cpmap0
            rw [List.length_tail, h0]
          obtain ⟨y, hy⟩ :
              ∃ y : (cpmap ([] : CProg)).Dart, (cpmap ([] : CProg)).cpring.tail = [y] :=
            List.length_eq_one_iff.mp h2
          rw [hy, Hypermap.insertE_cons, Hypermap.insertE_nil]
          refine List.nodup_cons.mpr ⟨fun hc => ?_, List.nodup_singleton _⟩
          exact PointedMap.plain_cpmap0.edge_ne y (List.mem_singleton.mp hc).symm
        have hcp : (cpmap [CpStep.Y]).cpring
            = (cpmap [CpStep.Y]).map.node (EcpDart.X : (cpmap [CpStep.Y]).Dart)
              :: (EcpDart.X : (cpmap [CpStep.Y]).Dart)
              :: ((cpmap ([] : CProg)).cpring.tail).map (injcpStep CpStep.Y []) :=
          PointedMap.cpring_ecpY' (cpmap [])
        have hlist : (cpmap [CpStep.Y]).cpring ++ ctrenum [CpStep.Y]
            = (cpmap [CpStep.Y]).map.node (EcpDart.X : (cpmap [CpStep.Y]).Dart)
              :: (EcpDart.X : (cpmap [CpStep.Y]).Dart)
              :: ((cpmap ([] : CProg)).cpring.tail).map (injcpStep CpStep.Y []) := by
          rw [ctrenum_Y_nil, List.append_nil, hcp]
        rw [hlist]
        exact nodup_insertE_ecpY (cpmap []) hbase
      | cons t cp =>
        have hih := ih (h.of_cons (by simp))
        have hh : (cpmap (t :: cp)).cpring
            = (cpmap (t :: cp)).map.node (cpmap (t :: cp)).point
              :: (cpmap (t :: cp)).cpring.tail := Hypermap.head_cpring
        have hperm : ((cpmap (t :: cp)).cpring.tail
              ++ ((cpmap (t :: cp)).map.node (cpmap (t :: cp)).point :: ctrenum (t :: cp))).Perm
            ((cpmap (t :: cp)).cpring ++ ctrenum (t :: cp)) := by
          refine List.Perm.symm ?_
          conv_lhs => rw [hh]
          exact List.perm_middle.symm
        have hcp : (cpmap (.Y :: t :: cp)).cpring
            = (cpmap (.Y :: t :: cp)).map.node (EcpDart.X : (cpmap (.Y :: t :: cp)).Dart)
              :: (EcpDart.X : (cpmap (.Y :: t :: cp)).Dart)
              :: ((cpmap (t :: cp)).cpring.tail).map (injcpStep CpStep.Y (t :: cp)) :=
          PointedMap.cpring_ecpY' (cpmap (t :: cp))
        have hlist : (cpmap (.Y :: t :: cp)).cpring ++ ctrenum (.Y :: t :: cp)
            = (cpmap (.Y :: t :: cp)).map.node (EcpDart.X : (cpmap (.Y :: t :: cp)).Dart)
              :: (EcpDart.X : (cpmap (.Y :: t :: cp)).Dart)
              :: (((cpmap (t :: cp)).cpring.tail
                  ++ ((cpmap (t :: cp)).map.node (cpmap (t :: cp)).point
                      :: ctrenum (t :: cp))).map (injcpStep CpStep.Y (t :: cp))) := by
          rw [ctrenum_Y_cons, List.map_append, hcp]
          rfl
        rw [hlist]
        exact nodup_insertE_ecpY (cpmap (t :: cp))
          ((insertE_perm (cpmap (t :: cp)).map hperm).nodup_iff.mpr hih)
    | H =>
      have hnil : cp ≠ [] := by rintro rfl; exact absurd h.2 (by simp)
      have hcfg := h.of_cons hnil
      have hih := ih hcfg
      have hp : (cpmap cp).Proper := cpmap_proper hcfg.cubicProg
      have hh : (cpmap cp).cpring
          = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
            :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
      have hperm : ((cpmap cp).cpring.drop 2
            ++ ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: ctrenum cp)).Perm
          ((cpmap cp).cpring ++ ctrenum cp) := by
        refine List.Perm.symm ?_
        conv_lhs => rw [hh]
        exact (List.perm_middle.trans (List.perm_middle.cons _)).symm
      have hcp : (cpmap (.H :: cp)).cpring
          = (cpmap (.H :: cp)).map.node (EcpDart.X : (cpmap (.H :: cp)).Dart)
            :: (EcpDart.X : (cpmap (.H :: cp)).Dart)
            :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
        PointedMap.cpring_ecpH' (cpmap cp) hp
      have hlist : (cpmap (.H :: cp)).cpring ++ ctrenum (.H :: cp)
          = (cpmap (.H :: cp)).map.node (EcpDart.X : (cpmap (.H :: cp)).Dart)
            :: (EcpDart.X : (cpmap (.H :: cp)).Dart)
            :: (((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp)
                ++ (cpmap (.H :: cp)).map.face (EcpDart.X : (cpmap (.H :: cp)).Dart)
                    :: ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
                        :: ctrenum cp).map (injcpStep CpStep.H cp)) := by
        rw [ctrenum_H, hcp]
        rfl
      rw [hlist]
      exact nodup_insertE_ecpH (cpmap cp) hp
        ((insertE_perm (cpmap cp).map hperm).nodup_iff.mpr hih)

/-! ### The contracted construction program

`cfctr cp mr mc` returns the program of the map obtained from `cpmap cp` by
contracting the kernel edges selected by `mc` and the ring edges selected by
`mr`.  Only the recursive calls ever select ring edges: the top-level call is
made with an all-`false` ring mask.  The computation fails, returning `none`,
as soon as it meets a step that is not a configuration step or a junction at
which two of the contracted edges share a node. -/

/-- The sparseness test at a junction: `notSparse b₁ b₂ b₃` holds when erasing
the edges selected by `b₁`, `b₂` and `b₃` around one junction would contract two
edges of a single node.  When the central edge `b₁` is erased any second erased
edge is fatal; otherwise only the two side edges together are. -/
def notSparse (b₁ b₂ b₃ : Bool) : Bool := if b₁ then b₂ || b₃ else b₂ && b₃

/-- The construction program of the contracted map, or `none` if the contract is
not sparse or `cp` is not a configuration program.  The ring mask `mr` lists the
ring darts whose edge is contracted, and `mc` the kernel edges; both are read
from the head of the ring and of `ctrenum cp` respectively. -/
def cfctr : CProg → List Bool → List Bool → Option CProg
  | .R i :: cp, mr, mc =>
      (cfctr cp (rotrMask i mr) mc).map fun cpc =>
        .R (((rotrMask i mr).take (i % mr.length)).count false) :: cpc
  | .Y :: [], b₁ :: b₂ :: b₃ :: _, _ =>
      if notSparse b₁ b₂ b₃ then none
      else some (if b₁ || b₂ || b₃ then [] else [.Y])
  | .Y :: s :: cp, b₁ :: b₂ :: mr, b₃ :: mc =>
      if notSparse b₁ b₂ b₃ then none
      else (cfctr (s :: cp) (b₃ :: mr) mc).map fun cpc =>
        if b₁ || b₂ then cpc else (if b₃ then .U else .Y) :: cpc
  | .H :: cp, b₁ :: b₂ :: mr, b₃ :: b₄ :: b₅ :: mc =>
      if notSparse b₃ b₁ b₄ || notSparse b₃ b₂ b₅ then none
      else if b₁ && b₂ && mr.all id then none
      else (cfctr cp (b₄ :: b₅ :: mr) mc).map fun cpc =>
        if b₃ then cpc
        else if b₁ then (if b₂ then .A :: cpc else if b₅ then cpc else .K :: cpc)
        else if b₂ then (if b₄ then cpc else .K :: cpc)
        else if b₄ then (if b₅ then .U :: cpc else .Y :: cpc)
        else if b₅ then .Y :: cpc else .H :: cpc
  | _, _, _ => none

@[simp] theorem cfctr_R (i : ℕ) (cp : CProg) (mr mc : List Bool) :
    cfctr (.R i :: cp) mr mc
      = (cfctr cp (rotrMask i mr) mc).map fun cpc =>
          .R (((rotrMask i mr).take (i % mr.length)).count false) :: cpc := rfl

@[simp] theorem cfctr_Y_nil (b₁ b₂ b₃ : Bool) (mr mc : List Bool) :
    cfctr [.Y] (b₁ :: b₂ :: b₃ :: mr) mc
      = if notSparse b₁ b₂ b₃ then none
        else some (if b₁ || b₂ || b₃ then [] else [.Y]) := rfl

@[simp] theorem cfctr_Y_cons (s : CpStep) (cp : CProg) (b₁ b₂ b₃ : Bool) (mr mc : List Bool) :
    cfctr (.Y :: s :: cp) (b₁ :: b₂ :: mr) (b₃ :: mc)
      = if notSparse b₁ b₂ b₃ then none
        else (cfctr (s :: cp) (b₃ :: mr) mc).map fun cpc =>
          if b₁ || b₂ then cpc else (if b₃ then .U else .Y) :: cpc := rfl

@[simp] theorem cfctr_H (cp : CProg) (b₁ b₂ b₃ b₄ b₅ : Bool) (mr mc : List Bool) :
    cfctr (.H :: cp) (b₁ :: b₂ :: mr) (b₃ :: b₄ :: b₅ :: mc)
      = if notSparse b₃ b₁ b₄ || notSparse b₃ b₂ b₅ then none
        else if b₁ && b₂ && mr.all id then none
        else (cfctr cp (b₄ :: b₅ :: mr) mc).map fun cpc =>
          if b₃ then cpc
          else if b₁ then (if b₂ then .A :: cpc else if b₅ then cpc else .K :: cpc)
          else if b₂ then (if b₄ then cpc else .K :: cpc)
          else if b₄ then (if b₅ then .U :: cpc else .Y :: cpc)
          else if b₅ then .Y :: cpc else .H :: cpc := rfl

@[simp] theorem cfctr_nil (mr mc : List Bool) : cfctr [] mr mc = none := rfl

/-- Adding a configuration step to a configuration program. -/
private theorem consConfigProg {s : CpStep} {cp : CProg} (hs : s.IsConfig)
    (h : ConfigProg cp) : ConfigProg (s :: cp) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hs
    · exact h.1 t ht
  · match cp, h.ne_nil with
    | t :: cp', _ => simpa using h.2

/-- **`cfctr` only succeeds on configuration programs.**  This is what turns the
dynamic contract computation into a proof that the program it ran on was a
configuration program. -/
theorem ConfigProg.of_cfctr : ∀ {cp : CProg} {mr mc : List Bool} {cpc : CProg},
    cfctr cp mr mc = some cpc → ConfigProg cp := by
  intro cp
  induction cp with
  | nil => intro mr mc cpc h; simp at h
  | cons s cp ih =>
    intro mr mc cpc h
    cases s with
    | R i =>
      rw [cfctr_R] at h
      obtain ⟨cpc', h', -⟩ := Option.map_eq_some_iff.mp h
      exact consConfigProg trivial (ih h')
    | R' => simp [cfctr] at h
    | Y =>
      cases cp with
      | nil =>
        refine ⟨fun t ht => ?_, rfl⟩
        simp only [List.mem_singleton] at ht
        subst ht
        exact trivial
      | cons t cp =>
        match mr, mc with
        | [], _ => simp [cfctr] at h
        | [_], _ => simp [cfctr] at h
        | _ :: _ :: _, [] => simp [cfctr] at h
        | b₁ :: b₂ :: mr, b₃ :: mc =>
          rw [cfctr_Y_cons] at h
          split at h
          · simp at h
          · obtain ⟨cpc', h', -⟩ := Option.map_eq_some_iff.mp h
            exact consConfigProg trivial (ih h')
    | H =>
      match mr, mc with
      | [], _ => simp [cfctr] at h
      | [_], _ => simp [cfctr] at h
      | _ :: _ :: _, [] => simp [cfctr] at h
      | _ :: _ :: _, [_] => simp [cfctr] at h
      | _ :: _ :: _, [_, _] => simp [cfctr] at h
      | b₁ :: b₂ :: mr, b₃ :: b₄ :: b₅ :: mc =>
        rw [cfctr_H] at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · obtain ⟨cpc', h', -⟩ := Option.map_eq_some_iff.mp h
            exact consConfigProg trivial (ih h')
    | U => simp [cfctr] at h
    | K => simp [cfctr] at h
    | A => simp [cfctr] at h

/-- A list of bits that is not all-`true` contains a `false`. -/
private theorem count_false_pos_of_not_all {mr : List Bool} (h : ¬ mr.all id = true) :
    0 < mr.count false := by
  rw [List.count_pos_iff]
  by_contra hmem
  refine h (List.all_eq_true.mpr fun x hx => ?_)
  cases x
  · exact absurd hx hmem
  · rfl

/-- **The ring size of the contracted map**: the contracted map has one ring
dart for every ring dart of `cpmap cp` whose edge is not erased by `mr`. -/
theorem cprsize_cfctr : ∀ {cp : CProg} {mr mc : List Bool} {cpc : CProg},
    mr.length = cprsize cp → mc.length = ctrmsize cp → cfctr cp mr mc = some cpc →
    cprsize cpc = mr.count false := by
  intro cp
  induction cp with
  | nil => intro mr mc cpc _ _ h; simp at h
  | cons s cp ih =>
    intro mr mc cpc hmr hmc h
    cases s with
    | R i =>
      rw [cfctr_R] at h
      obtain ⟨cpc', h', rfl⟩ := Option.map_eq_some_iff.mp h
      have hlen : (rotrMask i mr).length = cprsize cp := by
        simpa [cprsize] using hmr
      have hc := ih hlen (by simpa using hmc) h'
      have hcount : (rotrMask i mr).count false = mr.count false :=
        (List.rotate_perm mr (mr.length - i % mr.length)).count_eq false
      rw [show cprsize
            (CpStep.R (((rotrMask i mr).take (i % mr.length)).count false) :: cpc')
            = cprsize cpc' from rfl, hc, hcount]
    | R' => simp [cfctr] at h
    | U => simp [cfctr] at h
    | K => simp [cfctr] at h
    | A => simp [cfctr] at h
    | Y =>
      cases cp with
      | nil =>
        rw [show cprsize [CpStep.Y] = 3 from rfl, List.length_eq_three] at hmr
        obtain ⟨b₁, b₂, b₃, rfl⟩ := hmr
        rw [cfctr_Y_nil] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hns
          obtain rfl : (if b₁ || b₂ || b₃ then [] else [CpStep.Y]) = cpc := by
            simpa using h
          revert hns
          cases b₁ <;> cases b₂ <;> cases b₃ <;> decide
      | cons t cp =>
        match mr, mc with
        | [], _ => simp [cfctr] at h
        | [_], _ => simp [cfctr] at h
        | _ :: _ :: _, [] => simp [cfctr] at h
        | b₁ :: b₂ :: mr, b₃ :: mc =>
          rw [cfctr_Y_cons] at h
          split at h
          · exact absurd h (by simp)
          · rename_i hns
            obtain ⟨cpc', h', rfl⟩ := Option.map_eq_some_iff.mp h
            have hlen : (b₃ :: mr).length = cprsize (t :: cp) := by
              simp only [cprsize, List.length_cons] at hmr ⊢
              omega
            have hc := ih hlen (by simpa using hmc) h'
            revert hns hc
            cases b₁ <;> cases b₂ <;> cases b₃ <;>
              simp_all [notSparse, cprsize]
    | H =>
      match mr, mc with
      | [], _ => simp [cfctr] at h
      | [_], _ => simp [cfctr] at h
      | _ :: _ :: _, [] => simp [cfctr] at h
      | _ :: _ :: _, [_] => simp [cfctr] at h
      | _ :: _ :: _, [_, _] => simp [cfctr] at h
      | b₁ :: b₂ :: mr, b₃ :: b₄ :: b₅ :: mc =>
        rw [cfctr_H] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hns
          split at h
          · exact absurd h (by simp)
          · rename_i hall
            obtain ⟨cpc', h', rfl⟩ := Option.map_eq_some_iff.mp h
            have hlen : (b₄ :: b₅ :: mr).length = cprsize cp := by
              simp only [cprsize, List.length_cons] at hmr ⊢
              omega
            have hc := ih hlen (by simpa using hmc) h'
            have hpos : b₁ && b₂ → 0 < mr.count false := by
              intro hb
              refine count_false_pos_of_not_all fun hm => hall ?_
              simp [hb, hm]
            revert hns hall hpos hc
            cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;>
              simp_all [notSparse, cprsize, sub2ifgt2]

/-- Selecting a `true` bit. -/
private theorem listMask_true {α : Type*} (m : List Bool) (x : α) (l : List α) :
    listMask (true :: m) (x :: l) = x :: listMask m l := rfl

/-- Selecting a `false` bit. -/
private theorem listMask_false {α : Type*} (m : List Bool) (x : α) (l : List α) :
    listMask (false :: m) (x :: l) = listMask m l := rfl

/-! ### The band of a contract

`ctrband cm cp` selects the faces of `cpmap cp` incident to one of the edges
selected by the contract mask `cm`; both kernel and ring faces may occur. -/

/-- The mask of the faces incident to a contract edge.  A `Y` step adds the
selected edge to its two outer ring faces, and an `H` step spreads the three
edges it contributes over its two outer ring faces and the kernel face it
closes. -/
def ctrband : CProg → List Bool → CfMask
  | .R n :: cp, cm => let m := ctrband cp cm; ⟨m.ring.rotate n, m.kernel⟩
  | .Y :: [], _ => ⟨[false, false, false], []⟩
  | .Y :: s :: cp, b₁ :: cm =>
      match ctrband (s :: cp) cm with
      | ⟨a₀ :: a₁ :: mr, mk⟩ => ⟨(b₁ || a₀) :: false :: (b₁ || a₁) :: mr, mk⟩
      | _ => ⟨[], []⟩
  | .H :: cp, b₁ :: b₀ :: b₂ :: cm =>
      match ctrband cp cm with
      | ⟨a₀ :: a₁ :: a₂ :: mr, mk⟩ =>
          ⟨(b₀ || a₀) :: b₁ :: (b₂ || a₂) :: mr, (b₀ || b₁ || b₂ || a₁) :: mk⟩
      | _ => ⟨[], []⟩
  | _, _ => ⟨[], []⟩

@[simp] theorem ctrband_R (n : ℕ) (cp : CProg) (cm : List Bool) :
    ctrband (.R n :: cp) cm
      = ⟨(ctrband cp cm).ring.rotate n, (ctrband cp cm).kernel⟩ := rfl

@[simp] theorem ctrband_Y_nil (cm : List Bool) :
    ctrband [.Y] cm = ⟨[false, false, false], []⟩ := rfl

/-- One `Y` step of the band computation, when the ring mask of the recursive
call is long enough to be split. -/
theorem ctrband_Y_cons (s : CpStep) (cp : CProg) (b₁ : Bool) (cm : List Bool)
    (a₀ a₁ : Bool) (mr mk : List Bool) (h : ctrband (s :: cp) cm = ⟨a₀ :: a₁ :: mr, mk⟩) :
    ctrband (.Y :: s :: cp) (b₁ :: cm)
      = ⟨(b₁ || a₀) :: false :: (b₁ || a₁) :: mr, mk⟩ := by
  change (match ctrband (s :: cp) cm with
        | ⟨a₀ :: a₁ :: mr, mk⟩ =>
            (⟨(b₁ || a₀) :: false :: (b₁ || a₁) :: mr, mk⟩ : CfMask)
        | _ => ⟨[], []⟩) = _
  rw [h]

/-- One `H` step of the band computation, when the ring mask of the recursive
call is long enough to be split. -/
theorem ctrband_H_cons (cp : CProg) (b₁ b₀ b₂ : Bool) (cm : List Bool)
    (a₀ a₁ a₂ : Bool) (mr mk : List Bool)
    (h : ctrband cp cm = ⟨a₀ :: a₁ :: a₂ :: mr, mk⟩) :
    ctrband (.H :: cp) (b₁ :: b₀ :: b₂ :: cm)
      = ⟨(b₀ || a₀) :: b₁ :: (b₂ || a₂) :: mr, (b₀ || b₁ || b₂ || a₁) :: mk⟩ := by
  change (match ctrband cp cm with
        | ⟨a₀ :: a₁ :: a₂ :: mr, mk⟩ =>
            (⟨(b₀ || a₀) :: b₁ :: (b₂ || a₂) :: mr, (b₀ || b₁ || b₂ || a₁) :: mk⟩ : CfMask)
        | _ => ⟨[], []⟩) = _
  rw [h]

/-- A configuration map has at least three ring darts, since the program ends
with a `Y` step. -/
theorem three_le_cprsize : ∀ {cp : CProg}, ConfigProg cp → 3 ≤ cprsize cp := by
  intro cp
  induction cp with
  | nil => intro h; exact absurd h.2 (by simp)
  | cons s cp ih =>
    intro h
    by_cases hnil : cp = []
    · subst hnil
      have : s = CpStep.Y := by simpa using h.2
      subst this
      exact le_refl 3
    · have hc := ih (h.of_cons hnil)
      have hs := h.1 s List.mem_cons_self
      cases s with
      | R n => exact hc
      | R' => exact hs.elim
      | Y => simp only [cprsize]; omega
      | H => exact hc
      | U => exact hs.elim
      | K => exact hs.elim
      | A => exact hs.elim

/-- **The band of a contract is a proper mask.** -/
theorem properCfMask_ctrband : ∀ {cp : CProg}, ConfigProg cp → ∀ {cm : List Bool},
    cm.length = ctrmsize cp → (ctrband cp cm).Proper cp := by
  intro cp
  induction cp with
  | nil => intro h; exact absurd h.2 (by simp)
  | cons s cp ih =>
    intro h cm hcm
    have hs := h.1 s List.mem_cons_self
    cases s with
    | R' => exact hs.elim
    | U => exact hs.elim
    | K => exact hs.elim
    | A => exact hs.elim
    | R n =>
      have hnil : cp ≠ [] := by rintro rfl; exact absurd h.2 (by simp)
      obtain ⟨h₁, h₂⟩ := ih (h.of_cons hnil) (by simpa using hcm)
      exact ⟨by simpa [cprsize] using h₁, by simpa [cpksize] using h₂⟩
    | Y =>
      cases cp with
      | nil => exact ⟨rfl, rfl⟩
      | cons t cp =>
        have hcfg := h.of_cons (by simp)
        match cm, hcm with
        | b₁ :: cm, hcm =>
          have hcm' : cm.length = ctrmsize (t :: cp) := by
            simp only [ctrmsize_Y_cons, List.length_cons] at hcm; omega
          obtain ⟨h₁, h₂⟩ := ih hcfg hcm'
          have h3 := three_le_cprsize hcfg
          obtain ⟨a₀, a₁, mr, hr⟩ :
              ∃ a₀ a₁ mr, (ctrband (t :: cp) cm).ring = a₀ :: a₁ :: mr := by
            match hh : (ctrband (t :: cp) cm).ring with
            | a₀ :: a₁ :: mr => exact ⟨a₀, a₁, mr, rfl⟩
            | [] => rw [hh] at h₁; simp at h₁; omega
            | [a₀] => rw [hh] at h₁; simp at h₁; omega
          have hb : ctrband (t :: cp) cm = ⟨a₀ :: a₁ :: mr, (ctrband (t :: cp) cm).kernel⟩ := by
            rw [← hr]
          rw [ctrband_Y_cons t cp b₁ cm a₀ a₁ mr _ hb]
          rw [hr] at h₁
          exact ⟨by simp only [cprsize, List.length_cons] at h₁ ⊢; omega, h₂⟩
    | H =>
      have hnil : cp ≠ [] := by rintro rfl; exact absurd h.2 (by simp)
      have hcfg := h.of_cons hnil
      match cm, hcm with
      | b₁ :: b₀ :: b₂ :: cm, hcm =>
        have hcm' : cm.length = ctrmsize cp := by
          simp only [ctrmsize_H, List.length_cons] at hcm; omega
        obtain ⟨h₁, h₂⟩ := ih hcfg hcm'
        have h3 := three_le_cprsize hcfg
        obtain ⟨a₀, a₁, a₂, mr, hr⟩ :
            ∃ a₀ a₁ a₂ mr, (ctrband cp cm).ring = a₀ :: a₁ :: a₂ :: mr := by
          match hh : (ctrband cp cm).ring with
          | a₀ :: a₁ :: a₂ :: mr => exact ⟨a₀, a₁, a₂, mr, rfl⟩
          | [] => rw [hh] at h₁; simp at h₁; omega
          | [a₀] => rw [hh] at h₁; simp at h₁; omega
          | [a₀, a₁] => rw [hh] at h₁; simp at h₁; omega
        have hb : ctrband cp cm = ⟨a₀ :: a₁ :: a₂ :: mr, (ctrband cp cm).kernel⟩ := by
          rw [← hr]
        rw [ctrband_H_cons cp b₁ b₀ b₂ cm a₀ a₁ a₂ mr _ hb]
        rw [hr] at h₁
        exact ⟨by simp only [cprsize, List.length_cons] at h₁ ⊢; omega,
          by simp only [cpksize, List.length_cons, h₂]⟩

/-! ### The band of a contract is the band of its edges

`ctrband cp cm` returns a mask selecting exactly the faces of `cpmap cp` that
meet the edge closure of the contract selected by `cm`. -/

/-- The face band only depends on the darts of the list. -/
private theorem fband_perm {D : Type*} {G : Hypermap D} {p q : List D} (h : p.Perm q)
    (x : D) : G.Fband p x ↔ G.Fband q x := by
  constructor <;> rintro ⟨y, hy, hc⟩
  · exact ⟨y, h.mem_iff.mp hy, hc⟩
  · exact ⟨y, h.mem_iff.mpr hy, hc⟩

/-- The face band only depends on the face of the dart. -/
private theorem fband_cface {D : Type*} {G : Hypermap D} {p : List D} {x y : D}
    (h : G.CFace x y) : G.Fband p x ↔ G.Fband p y := by
  constructor <;> rintro ⟨z, hz, hc⟩
  · exact ⟨z, hz, h.symm.trans hc⟩
  · exact ⟨z, hz, h.trans hc⟩

/-- Lying on a given face only depends on the face of the second dart. -/
private theorem cface_congr_right {D : Type*} {G : Hypermap D} {y z : D} (h : G.CFace y z)
    (x : D) : G.CFace x y ↔ G.CFace x z :=
  ⟨fun hx => hx.trans h, fun hx => hx.trans h.symm⟩

/-- Lying on a given face only depends on the face of the first dart. -/
private theorem cface_congr_left {D : Type*} {G : Hypermap D} {x y : D} (h : G.CFace x y)
    (z : D) : G.CFace x z ↔ G.CFace y z :=
  ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

/-- The band of a masked list, one bit at a time. -/
private theorem fband_listMask_cons {D : Type*} (G : Hypermap D) (b : Bool) (m : List Bool)
    (y : D) (l : List D) (x : D) :
    G.Fband (listMask (b :: m) (y :: l)) x
      ↔ (b = true ∧ G.CFace x y) ∨ G.Fband (listMask m l) x := by
  cases b
  · simp [listMask_false]
  · simp [listMask_true]

/-- The band of the edge closure of a masked list, one bit at a time. -/
private theorem fband_insertE_listMask_cons {D : Type*} (G : Hypermap D) (b : Bool)
    (m : List Bool) (y : D) (l : List D) (x : D) :
    G.Fband (G.insertE (listMask (b :: m) (y :: l))) x
      ↔ (b = true ∧ (G.CFace x y ∨ G.CFace x (G.edge y)))
        ∨ G.Fband (G.insertE (listMask m l)) x := by
  cases b
  · simp [listMask_false]
  · simp [listMask_true, Hypermap.insertE_cons, or_assoc]

/-- The band of an image list, at the image of a dart. -/
private theorem fband_map_congr {D D' : Type*} {G : Hypermap D} {G' : Hypermap D'}
    {f : D → D'} (hf : ∀ y z : D, G'.CFace (f y) (f z) ↔ G.CFace y z) (p : List D) (x : D) :
    G'.Fband (p.map f) (f x) ↔ G.Fband p x := by
  simp only [Hypermap.Fband, List.mem_map]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hc⟩
    exact ⟨z, hz, (hf x z).mp hc⟩
  · rintro ⟨z, hz, hc⟩
    exact ⟨f z, ⟨z, hz, rfl⟩, (hf x z).mpr hc⟩

/-! #### Transferring the band along a construction step -/

/-- A `Y` step does not change the faces of the old darts. -/
private theorem cface_injcpY (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (.Y :: cp)).map.CFace (injcpStep .Y cp x) (injcpStep .Y cp y)
      ↔ (cpmap cp).map.CFace x y := PointedMap.cface_icpY' (cpmap cp) x y

/-- An `H` step does not change the faces of the old darts. -/
private theorem cface_injcpH (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (.H :: cp)).map.CFace (injcpStep .H cp x) (injcpStep .H cp y)
      ↔ (cpmap cp).map.CFace x y := PointedMap.cface_icpH' (cpmap cp) x y

/-- The band of the image of a list after a `Y` step. -/
private theorem fband_map_injcpY (cp : CProg) (p : List (cpmap cp).Dart)
    (x : (cpmap cp).Dart) :
    (cpmap (.Y :: cp)).map.Fband (p.map (injcpStep .Y cp)) (injcpStep .Y cp x)
      ↔ (cpmap cp).map.Fband p x := fband_map_congr (cface_injcpY cp) p x

/-- The band of the image of a list after an `H` step. -/
private theorem fband_map_injcpH (cp : CProg) (p : List (cpmap cp).Dart)
    (x : (cpmap cp).Dart) :
    (cpmap (.H :: cp)).map.Fband (p.map (injcpStep .H cp)) (injcpStep .H cp x)
      ↔ (cpmap cp).map.Fband p x := fband_map_congr (cface_injcpH cp) p x

/-- The node of the new dart of a `Y` step lies on the face of the old ring
head. -/
private theorem cface_injcpY_node (cp : CProg) (x : (cpmap cp).Dart) :
    (cpmap (.Y :: cp)).map.CFace (injcpStep .Y cp x)
        ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
      ↔ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point) :=
  (cface_congr_right (PointedMap.cface_node_ecpY' (cpmap cp)) _).trans (cface_injcpY cp x _)

/-- The node of the new dart of an `H` step lies on the face of the old ring
head. -/
private theorem cface_injcpH_node (cp : CProg) (hp : (cpmap cp).Proper)
    (x : (cpmap cp).Dart) :
    (cpmap (.H :: cp)).map.CFace (injcpStep .H cp x)
        ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      ↔ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point) :=
  (cface_congr_right (PointedMap.cface_node_ecpH' (cpmap cp) hp) _).trans (cface_injcpH cp x _)

/-- The new face of a `Y` step is not the face of an old dart. -/
private theorem not_cface_injcpY (cp : CProg) (x : (cpmap cp).Dart) :
    ¬ (cpmap (.Y :: cp)).map.CFace (cpmap (.Y :: cp)).point (injcpStep .Y cp x) :=
  PointedMap.not_cface_ecpY_icpY (cpmap cp) x

/-- The new face of an `H` step is not the face of an old dart. -/
private theorem not_cface_injcpH (cp : CProg) (hp : (cpmap cp).Proper) (x : (cpmap cp).Dart) :
    ¬ (cpmap (.H :: cp)).map.CFace (cpmap (.H :: cp)).point (injcpStep .H cp x) :=
  PointedMap.not_cface_ecpH_icpH (cpmap cp) hp x

/-- The new face of a `Y` step meets no image of an old dart. -/
private theorem not_fband_map_injcpY (cp : CProg) (p : List (cpmap cp).Dart)
    {u : (cpmap (.Y :: cp)).Dart}
    (hu : (cpmap (.Y :: cp)).map.CFace (cpmap (.Y :: cp)).point u) :
    ¬ (cpmap (.Y :: cp)).map.Fband (p.map (injcpStep .Y cp)) u := by
  rintro ⟨y, hy, hc⟩
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
  exact not_cface_injcpY cp z (hu.trans hc)

/-- The new face of an `H` step meets no image of an old dart. -/
private theorem not_fband_map_injcpH (cp : CProg) (hp : (cpmap cp).Proper)
    (p : List (cpmap cp).Dart) {u : (cpmap (.H :: cp)).Dart}
    (hu : (cpmap (.H :: cp)).map.CFace (cpmap (.H :: cp)).point u) :
    ¬ (cpmap (.H :: cp)).map.Fband (p.map (injcpStep .H cp)) u := by
  rintro ⟨y, hy, hc⟩
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
  exact not_cface_injcpH cp hp z (hu.trans hc)

/-- The new face of a `Y` step is not the face of the node of its new dart. -/
private theorem not_cface_node_injcpY (cp : CProg) {u : (cpmap (.Y :: cp)).Dart}
    (hu : (cpmap (.Y :: cp)).map.CFace (cpmap (.Y :: cp)).point u) :
    ¬ (cpmap (.Y :: cp)).map.CFace u
      ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point) := fun hc =>
  not_cface_injcpY cp ((cpmap cp).map.node (cpmap cp).point)
    ((hu.trans hc).trans (PointedMap.cface_node_ecpY' (cpmap cp)))

/-- The new face of an `H` step is not the face of the node of its new dart. -/
private theorem not_cface_node_injcpH (cp : CProg) (hp : (cpmap cp).Proper)
    {u : (cpmap (.H :: cp)).Dart}
    (hu : (cpmap (.H :: cp)).map.CFace (cpmap (.H :: cp)).point u) :
    ¬ (cpmap (.H :: cp)).map.CFace u
      ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point) := fun hc =>
  not_cface_injcpH cp hp ((cpmap cp).map.node (cpmap cp).point)
    ((hu.trans hc).trans (PointedMap.cface_node_ecpH' (cpmap cp) hp))

/-- Every dart of a `Y` step map lies on the face of an old dart or on the new
face. -/
private theorem fband_injcpY (cp : CProg) (u : (cpmap (.Y :: cp)).Dart) :
    (∃ x : (cpmap cp).Dart, (cpmap (.Y :: cp)).map.CFace u (injcpStep .Y cp x))
      ∨ (cpmap (.Y :: cp)).map.CFace (cpmap (.Y :: cp)).point u :=
  PointedMap.fband_icpY' (cpmap cp) u

/-- Every dart of an `H` step map lies on the face of an old dart or on the new
face. -/
private theorem fband_injcpH (cp : CProg) (u : (cpmap (.H :: cp)).Dart) :
    (∃ x : (cpmap cp).Dart, (cpmap (.H :: cp)).map.CFace u (injcpStep .H cp x))
      ∨ (cpmap (.H :: cp)).map.CFace (cpmap (.H :: cp)).point u :=
  PointedMap.fband_icpH' (cpmap cp) u

/-- **The second dart of the crossbar of an `H` step** lies on the face of the
old reference dart: that is the kernel face the step closes. -/
private theorem cface_edge_face_ecpH (M : PointedMap) (hp : M.Proper) :
    M.ecpH.map.CFace (M.ecpH.map.edge (M.ecpH.map.face M.ecpH.point)) (M.icpH M.point) := by
  have hnn : (Hypermap.ecpUMap M.map M.point).node⁻¹
      ((Hypermap.ecpUMap M.map M.point).node⁻¹ (EcpDart.X : EcpDart M.Dart))
      = EcpDart.icp M.point := by
    rw [Hypermap.node_inv_ecpU_X M.map M.point,
      Hypermap.node_inv_ecpU_icp_node M.map M.point hp]
  have hXeY : (Hypermap.ecpNMap (Hypermap.ecpUMap M.map M.point) EcpDart.X).CFace
      EcpDart.Xe (EcpDart.icp (EcpDart.icp M.point)) := by
    refine (Hypermap.cface_Xe_icpN (Hypermap.ecpUMap M.map M.point) EcpDart.X
      (EcpDart.icp M.point)).mpr ?_
    rw [hnn]
  exact (Hypermap.cface_icpN (Hypermap.ecpNMap (Hypermap.ecpUMap M.map M.point) EcpDart.X)
    EcpDart.X EcpDart.Xe (EcpDart.icp (EcpDart.icp M.point))).mpr hXeY

/-! #### The recursive step of the band computation -/

/-- The kernel transversal is unchanged by a rotation step. -/
private theorem cpker_R (n : ℕ) (cp : CProg) : cpker (.R n :: cp) = cpker cp := rfl

/-- The kernel edge transversal of a `Y` step over a nonempty program. -/
private theorem ctrenum_Y' (cp : CProg) (h : cp ≠ []) :
    ctrenum (.Y :: cp)
      = ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp).map (injcpStep .Y cp) := by
  match cp, h with
  | _ :: _, _ => rfl

/-- The band of a `Y` step over a nonempty program. -/
private theorem ctrband_Y' (cp : CProg) (h : cp ≠ []) (b : Bool) (cm : List Bool)
    {a₀ a₁ : Bool} {mr mk : List Bool} (hb : ctrband cp cm = ⟨a₀ :: a₁ :: mr, mk⟩) :
    ctrband (.Y :: cp) (b :: cm) = ⟨(b || a₀) :: false :: (b || a₁) :: mr, mk⟩ := by
  match cp, h with
  | s :: cp, _ => exact ctrband_Y_cons s cp b cm a₀ a₁ mr mk hb

/-- Merging one new contract edge into the two ring bits it meets. -/
private theorem or_merge_two {b a₀ a₁ : Bool} {P₀ P₁ Q : Prop} :
    ((b = true ∧ (P₀ ∨ P₁)) ∨ ((a₀ = true ∧ P₀) ∨ ((a₁ = true ∧ P₁) ∨ Q)))
      ↔ (((b || a₀) = true ∧ P₀) ∨ (((b || a₁) = true ∧ P₁) ∨ Q)) := by
  cases b <;> cases a₀ <;> cases a₁ <;> simp <;> tauto

/-- Merging the three new contract edges of an `H` step into the bits they
meet. -/
private theorem or_merge_three {b₀ b₁ b₂ a₀ a₁ a₂ : Bool} {P₀ P₁ P₂ R K : Prop} :
    ((b₁ = true ∧ P₁) ∨ ((b₀ = true ∧ (P₀ ∨ P₁)) ∨ ((b₂ = true ∧ (P₁ ∨ P₂))
        ∨ ((a₀ = true ∧ P₀) ∨ ((a₁ = true ∧ P₁) ∨ ((a₂ = true ∧ P₂) ∨ (R ∨ K)))))))
      ↔ (((b₀ || a₀) = true ∧ P₀) ∨ (((b₂ || a₂) = true ∧ P₂)
          ∨ (R ∨ (((b₀ || b₁ || b₂ || a₁) = true ∧ P₁) ∨ K)))) := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases a₀ <;> cases a₁ <;> cases a₂ <;>
    simp <;> tauto

/-- **The `Y` step of the band lemma.**  A `Y` step adds a single kernel edge;
its two faces are the two outer ring faces of the step. -/
private theorem ctrband_correct_Y {cp : CProg} (hcfg : ConfigProg cp) (b : Bool)
    {cm : List Bool} (hcm : cm.length = ctrmsize cp)
    (ih : ∀ x : (cpmap cp).Dart,
      (cpmap cp).map.Fband ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) x
        ↔ (cpmap cp).map.Fband (cpmask (ctrband cp cm) cp) x)
    (u : (cpmap (.Y :: cp)).Dart) :
    ((cpmap (.Y :: cp)).map.Fband
        ((cpmap (.Y :: cp)).map.insertE (listMask (b :: cm) (ctrenum (.Y :: cp)))) u
      ↔ (cpmap (.Y :: cp)).map.Fband
          (cpmask (ctrband (.Y :: cp) (b :: cm)) (.Y :: cp)) u) := by
  have hp : (cpmap cp).Proper := cpmap_proper hcfg.cubicProg
  obtain ⟨d2, hd2⟩ : ∃ d2, (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: d2 :=
    ⟨(cpmap cp).cpring.drop 2, Hypermap.head_proper_cpring hp⟩
  have hGtail : (cpmap cp).cpring.tail = (cpmap cp).point :: d2 := by rw [hd2]; rfl
  have hMring : (cpmap (.Y :: cp)).cpring
      = (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point :: (cpmap (.Y :: cp)).point
        :: ((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp) :=
    PointedMap.cpring_ecpY' (cpmap cp)
  obtain ⟨a₀, a₁, mr, kb, hb⟩ :
      ∃ a₀ a₁ mr kb, ctrband cp cm = ⟨a₀ :: a₁ :: mr, kb⟩ := by
    have h1 : (ctrband cp cm).ring.length = cprsize cp := (properCfMask_ctrband hcfg hcm).1
    have h3 := three_le_cprsize hcfg
    match hh : (ctrband cp cm).ring with
    | a₀ :: a₁ :: mr => exact ⟨a₀, a₁, mr, (ctrband cp cm).kernel, by rw [← hh]⟩
    | [] => rw [hh] at h1; simp at h1; omega
    | [_] => rw [hh] at h1; simp at h1; omega
  have hedgeNG : ∀ z : (cpmap cp).Dart,
      (cpmap cp).map.CFace z ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
        ↔ (cpmap cp).map.CFace z (cpmap cp).point := by
    intro z
    refine cface_congr_right ?_ z
    have h1 : (cpmap cp).map.face ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
        = (cpmap cp).point := by
      rw [Hypermap.face_edge, Hypermap.inv_node_node]
    have h2 := (cpmap cp).map.cface_face
      ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
    rw [h1] at h2
    exact h2
  have hLHSeq : (cpmap (.Y :: cp)).map.insertE (listMask (b :: cm) (ctrenum (.Y :: cp)))
      = ((cpmap cp).map.insertE
          (listMask (b :: cm) ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp))).map
            (injcpStep CpStep.Y cp) := by
    rw [ctrenum_Y' cp hcfg.ne_nil, listMask_map,
      insertE_map (cpmap cp).map (cpmap (.Y :: cp)).map (injcpStep CpStep.Y cp)
        (fun _ => rfl) _]
  have hRHSeq : cpmask (ctrband (.Y :: cp) (b :: cm)) (.Y :: cp)
      = listMask ((b || a₀) :: false :: (b || a₁) :: mr)
          ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point
            :: (cpmap (.Y :: cp)).point
            :: (injcpStep CpStep.Y cp (cpmap cp).point :: d2.map (injcpStep CpStep.Y cp)))
        ++ (listMask kb (cpker cp)).map (injcpStep CpStep.Y cp) := by
    simp only [cpmask, ctrband_Y' cp hcfg.ne_nil b cm hb, cpker_Y, listMask_map]
    rw [hMring, hGtail]
    rfl
  have hihx : ∀ x : (cpmap cp).Dart,
      (cpmap cp).map.Fband ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) x
        ↔ ((a₀ = true) ∧ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point))
          ∨ (((a₁ = true) ∧ (cpmap cp).map.CFace x (cpmap cp).point)
            ∨ ((cpmap cp).map.Fband (listMask mr d2) x
              ∨ (cpmap cp).map.Fband (listMask kb (cpker cp)) x)) := by
    intro x
    have hmk : cpmask (ctrband cp cm) cp
        = listMask (a₀ :: a₁ :: mr)
            ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: d2)
          ++ listMask kb (cpker cp) := by
      simp only [cpmask, hb]
      rw [hd2]
    rw [ih x, hmk]
    simp only [Hypermap.fband_append, fband_listMask_cons, or_assoc]
  rw [hLHSeq, hRHSeq]
  simp only [Hypermap.fband_append, fband_listMask_cons, listMask_map,
    Bool.false_eq_true, false_and, false_or, or_assoc]
  rcases fband_injcpY cp u with ⟨x, hx⟩ | hX
  · simp only [fband_cface hx, cface_congr_left hx, fband_map_injcpY,
      cface_injcpY_node, cface_injcpY, fband_insertE_listMask_cons, hedgeNG, hihx]
    exact or_merge_two
  · refine iff_of_false (not_fband_map_injcpY cp _ hX) ?_
    rintro (⟨-, hc⟩ | ⟨-, hc⟩ | hc | hc)
    · exact not_cface_node_injcpY cp hX hc
    · exact not_cface_injcpY cp _ (hX.trans hc)
    · exact not_fband_map_injcpY cp _ hX hc
    · exact not_fband_map_injcpY cp _ hX hc

/-- **The `H` step of the band lemma.**  An `H` step adds three kernel edges:
its crossbar, whose faces are the new face and the kernel face it closes, and
its two feet, whose faces are the outer ring faces and that same kernel face. -/
private theorem ctrband_correct_H {cp : CProg} (hcfg : ConfigProg cp) (b₁ b₀ b₂ : Bool)
    {cm : List Bool} (hcm : cm.length = ctrmsize cp)
    (ih : ∀ x : (cpmap cp).Dart,
      (cpmap cp).map.Fband ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) x
        ↔ (cpmap cp).map.Fband (cpmask (ctrband cp cm) cp) x)
    (u : (cpmap (.H :: cp)).Dart) :
    ((cpmap (.H :: cp)).map.Fband
        ((cpmap (.H :: cp)).map.insertE
          (listMask (b₁ :: b₀ :: b₂ :: cm) (ctrenum (.H :: cp)))) u
      ↔ (cpmap (.H :: cp)).map.Fband
          (cpmask (ctrband (.H :: cp) (b₁ :: b₀ :: b₂ :: cm)) (.H :: cp)) u) := by
  have hp : (cpmap cp).Proper := cpmap_proper hcfg.cubicProg
  have hlong : (cpmap cp).Long := cfmap_long hcfg
  obtain ⟨d3, hd3⟩ : ∃ d3, (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
        :: (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point) :: d3 :=
    ⟨(cpmap cp).cpring.drop 3, Hypermap.head_long_cpring hlong⟩
  have hGdrop : (cpmap cp).cpring.drop 2
      = (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point) :: d3 := by
    rw [hd3]; rfl
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hMker : cpker (.H :: cp)
      = ((cpmap cp).point :: cpker cp).map (injcpStep CpStep.H cp) :=
    cpker_H_point cp hp
  obtain ⟨a₀, a₁, a₂, mr, kb, hb⟩ :
      ∃ a₀ a₁ a₂ mr kb, ctrband cp cm = ⟨a₀ :: a₁ :: a₂ :: mr, kb⟩ := by
    have h1 : (ctrband cp cm).ring.length = cprsize cp := (properCfMask_ctrband hcfg hcm).1
    have h3 := three_le_cprsize hcfg
    match hh : (ctrband cp cm).ring with
    | a₀ :: a₁ :: a₂ :: mr => exact ⟨a₀, a₁, a₂, mr, (ctrband cp cm).kernel, by rw [← hh]⟩
    | [] => rw [hh] at h1; simp at h1; omega
    | [_] => rw [hh] at h1; simp at h1; omega
    | [_, _] => rw [hh] at h1; simp at h1; omega
  have hedgeNG : ∀ z : (cpmap cp).Dart,
      (cpmap cp).map.CFace z ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
        ↔ (cpmap cp).map.CFace z (cpmap cp).point := by
    intro z
    refine cface_congr_right ?_ z
    have h1 : (cpmap cp).map.face ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
        = (cpmap cp).point := by
      rw [Hypermap.face_edge, Hypermap.inv_node_node]
    have h2 := (cpmap cp).map.cface_face
      ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
    rw [h1] at h2
    exact h2
  have hedgePT : ∀ z : (cpmap cp).Dart,
      (cpmap cp).map.CFace z ((cpmap cp).map.edge (cpmap cp).point)
        ↔ (cpmap cp).map.CFace z
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) :=
    fun z => cface_congr_right ((cpmap cp).map.cface_face _) z
  have hfaceX : ∀ v : (cpmap (.H :: cp)).Dart,
      (cpmap (.H :: cp)).map.CFace v
          ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point)
        ↔ (cpmap (.H :: cp)).map.CFace v (cpmap (.H :: cp)).point :=
    fun v => (cface_congr_right ((cpmap (.H :: cp)).map.cface_face _) v).symm
  have hedgefaceX : ∀ v : (cpmap (.H :: cp)).Dart,
      (cpmap (.H :: cp)).map.CFace v
          ((cpmap (.H :: cp)).map.edge
            ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point))
        ↔ (cpmap (.H :: cp)).map.CFace v (injcpStep CpStep.H cp (cpmap cp).point) :=
    fun v => cface_congr_right (cface_edge_face_ecpH (cpmap cp) hp) v
  have hLHSeq : (cpmap (.H :: cp)).map.insertE
        (listMask (b₀ :: b₂ :: cm)
          (((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: ctrenum cp).map
            (injcpStep CpStep.H cp)))
      = ((cpmap cp).map.insertE
          (listMask (b₀ :: b₂ :: cm)
            ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: ctrenum cp))).map
              (injcpStep CpStep.H cp) := by
    rw [listMask_map, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map
      (injcpStep CpStep.H cp) (fun _ => rfl) _]
  have hRHSeq : cpmask (ctrband (.H :: cp) (b₁ :: b₀ :: b₂ :: cm)) (.H :: cp)
      = listMask ((b₀ || a₀) :: b₁ :: (b₂ || a₂) :: mr)
          ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
            :: (cpmap (.H :: cp)).point
            :: (injcpStep CpStep.H cp
                  ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))
                :: d3.map (injcpStep CpStep.H cp)))
        ++ listMask ((b₀ || b₁ || b₂ || a₁) :: kb)
            (injcpStep CpStep.H cp (cpmap cp).point
              :: (cpker cp).map (injcpStep CpStep.H cp)) := by
    simp only [cpmask, ctrband_H_cons cp b₁ b₀ b₂ cm a₀ a₁ a₂ mr kb hb]
    rw [hMring, hGdrop, hMker]
    rfl
  have hihx : ∀ x : (cpmap cp).Dart,
      (cpmap cp).map.Fband ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) x
        ↔ ((a₀ = true) ∧ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point))
          ∨ (((a₁ = true) ∧ (cpmap cp).map.CFace x (cpmap cp).point)
            ∨ (((a₂ = true) ∧ (cpmap cp).map.CFace x
                  ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)))
              ∨ ((cpmap cp).map.Fband (listMask mr d3) x
                ∨ (cpmap cp).map.Fband (listMask kb (cpker cp)) x))) := by
    intro x
    have hmk : cpmask (ctrband cp cm) cp
        = listMask (a₀ :: a₁ :: a₂ :: mr)
            ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
              :: (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point) :: d3)
          ++ listMask kb (cpker cp) := by
      simp only [cpmask, hb]
      rw [hd3]
    rw [ih x, hmk]
    simp only [Hypermap.fband_append, fband_listMask_cons, or_assoc]
  rw [ctrenum_H, hRHSeq, fband_insertE_listMask_cons, hLHSeq]
  simp only [Hypermap.fband_append, fband_listMask_cons, listMask_map, or_assoc]
  rcases fband_injcpH cp u with ⟨x, hx⟩ | hX
  · have hnotpt : ∀ y : (cpmap cp).Dart,
        (cpmap (.H :: cp)).map.CFace (injcpStep CpStep.H cp y)
            (cpmap (.H :: cp)).point ↔ False :=
      fun y => iff_false_intro (fun hc => not_cface_injcpH cp hp y hc.symm)
    simp only [fband_cface hx, cface_congr_left hx, hfaceX, hedgefaceX,
      fband_map_injcpH, cface_injcpH_node cp hp, cface_injcpH,
      fband_insertE_listMask_cons, hedgeNG, hedgePT, hihx, hnotpt,
      false_or, and_false]
    exact or_merge_three
  · have hpt : (cpmap (.H :: cp)).map.CFace u (cpmap (.H :: cp)).point ↔ True :=
      iff_true_intro hX.symm
    have hnX : (cpmap (.H :: cp)).map.CFace u
        ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point) ↔ False :=
      iff_false_intro (not_cface_node_injcpH cp hp hX)
    have himg : ∀ y : (cpmap cp).Dart,
        (cpmap (.H :: cp)).map.CFace u (injcpStep CpStep.H cp y) ↔ False :=
      fun y => iff_false_intro (fun hc => not_cface_injcpH cp hp y (hX.trans hc))
    have hfb : ∀ q : List (cpmap cp).Dart,
        (cpmap (.H :: cp)).map.Fband (q.map (injcpStep CpStep.H cp)) u ↔ False :=
      fun q => iff_false_intro (not_fband_map_injcpH cp hp q hX)
    simp only [hfaceX, hedgefaceX, hpt, hnX, himg, hfb, and_true, and_false,
      false_or, or_false]

/-- **`ctrband` computes the band of a contract**: the mask it returns selects
exactly the faces of `cpmap cp` that meet the edge closure of the contract. -/
theorem ctrband_correct : ∀ {cp : CProg}, ConfigProg cp → ∀ {cm : List Bool},
    cm.length = ctrmsize cp → ∀ u : (cpmap cp).Dart,
    ((cpmap cp).map.Fband ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) u
      ↔ (cpmap cp).map.Fband (cpmask (ctrband cp cm) cp) u) := by
  intro cp
  induction cp with
  | nil => intro h; exact absurd h.2 (by simp)
  | cons s cp ih =>
    intro h cm hcm u
    have hs := h.1 s List.mem_cons_self
    cases s with
    | R' => exact hs.elim
    | U => exact hs.elim
    | K => exact hs.elim
    | A => exact hs.elim
    | R n =>
      have hnil : cp ≠ [] := by rintro rfl; exact absurd h.2 (by simp)
      have hcfg := h.of_cons hnil
      have hcm' : cm.length = ctrmsize cp := by simpa using hcm
      have hlen : (ctrband cp cm).ring.length = (cpmap cp).cpring.length := by
        rw [(properCfMask_ctrband hcfg hcm').1, size_ring_cpmap]
      have hr : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
        Hypermap.cpring_ecpR (G := (cpmap cp).map) (x₀ := (cpmap cp).point) n
      have hmask : cpmask (ctrband (.R n :: cp) cm) (.R n :: cp)
          = listMask ((ctrband cp cm).ring.rotate n) ((cpmap cp).cpring.rotate n)
            ++ listMask (ctrband cp cm).kernel (cpker cp) := by
        simp only [cpmask, ctrband_R, cpker_R]
        rw [hr]
        rfl
      have hmaskG : cpmask (ctrband cp cm) cp
          = listMask (ctrband cp cm).ring (cpmap cp).cpring
            ++ listMask (ctrband cp cm).kernel (cpker cp) := rfl
      rw [ctrenum_R, hmask]
      refine (ih hcfg hcm' u).trans ?_
      rw [hmaskG]
      exact fband_perm
        (((listMask_rotate_perm (ctrband cp cm).ring (cpmap cp).cpring hlen n).symm).append_right
          _) u
    | Y =>
      cases cp with
      | nil =>
        obtain rfl : cm = [] := List.eq_nil_of_length_eq_zero (by simpa using hcm)
        refine iff_of_false ?_ ?_
        · rw [show listMask ([] : List Bool) (ctrenum [CpStep.Y]) = []
            from listMask_nil_mask _, Hypermap.insertE_nil]
          rintro ⟨y, hy, -⟩
          cases hy
        · rw [show cpmask (ctrband [CpStep.Y] []) [CpStep.Y]
              = listMask [false, false, false] (cpmap [CpStep.Y]).cpring
                ++ listMask ([] : List Bool) (cpker [CpStep.Y]) from rfl,
            listMask_eq_nil _ _ (by simp), listMask_nil_mask, List.append_nil]
          rintro ⟨y, hy, -⟩
          cases hy
      | cons t cp =>
        have hcfg := h.of_cons (by simp)
        match cm, hcm with
        | b :: cm, hcm =>
          have hcm' : cm.length = ctrmsize (t :: cp) := by
            simp only [ctrmsize_Y_cons, List.length_cons] at hcm; omega
          exact ctrband_correct_Y hcfg b hcm' (ih hcfg hcm') u
    | H =>
      have hnil : cp ≠ [] := by rintro rfl; exact absurd h.2 (by simp)
      have hcfg := h.of_cons hnil
      match cm, hcm with
      | b₁ :: b₀ :: b₂ :: cm, hcm =>
        have hcm' : cm.length = ctrmsize cp := by
          simp only [ctrmsize_H, List.length_cons] at hcm; omega
        exact ctrband_correct_H hcfg b₁ b₀ b₂ hcm' (ih hcfg hcm') u

/-! ### The contract colourings of the contracted map

`cfctr_correct` is the semantic counterpart of `cfctr`: a contract colouring of
`cpmap cp` for the contract selected by `mr` and `mc` restricts to a genuine
colouring of the contracted map `cpmap cpc`, whose ring trace is the trace of
the ring darts that the contract does *not* erase. -/

/-- A rotation commutes with the selection of a mask, up to a rotation of the
selection by the number of selected entries that move to the back. -/
private theorem listMask_rotate_le {α : Type*} : ∀ (n : ℕ) (m : List Bool) (l : List α),
    m.length = l.length → n ≤ m.length →
    listMask (m.rotate n) (l.rotate n) = (listMask m l).rotate ((m.take n).count true) := by
  intro n
  induction n with
  | zero => intro m l _ _; simp
  | succ n ih =>
    intro m l hlen hn
    match m, l, hlen, hn with
    | b :: m, x :: l, hlen, hn =>
      have hlen' : m.length = l.length := by simpa using hlen
      have hn' : n ≤ m.length := by simp only [List.length_cons] at hn; omega
      have hn2 : n ≤ (m ++ [b]).length := by simp only [List.length_append]; omega
      rw [List.rotate_cons_succ, List.rotate_cons_succ,
        ih (m ++ [b]) (l ++ [x]) (by simp [hlen']) hn2,
        listMask_append m l hlen' [b] [x], List.take_append_of_le_length hn']
      cases b
      · simp [listMask]
      · rw [show listMask [true] [x] = [x] from rfl,
          show listMask (true :: m) (x :: l) = x :: listMask m l from rfl]
        rw [show ((true :: m).take (n + 1)).count true = (m.take n).count true + 1 by
          simp [List.take_succ_cons]]
        rw [List.rotate_cons_succ]

/-- **A rotation commutes with mask selection.** -/
theorem listMask_rotate {α : Type*} (m : List Bool) (l : List α) (hlen : m.length = l.length)
    (n : ℕ) : listMask (m.rotate n) (l.rotate n)
      = (listMask m l).rotate ((m.take (n % m.length)).count true) := by
  rcases Nat.eq_zero_or_pos m.length with h0 | hpos
  · have hl : l = [] := List.eq_nil_of_length_eq_zero (by rw [← hlen, h0])
    have hm : m = [] := List.eq_nil_of_length_eq_zero h0
    subst hm; subst hl; simp
  · have hle : n % m.length ≤ m.length := le_of_lt (Nat.mod_lt _ hpos)
    have h2 : l.rotate n = l.rotate (n % m.length) := by
      rw [hlen]; exact (List.rotate_mod l n).symm
    rw [← List.rotate_mod m n, h2]
    exact listMask_rotate_le _ m l hlen hle

/-- Mapping commutes with rotation. -/
private theorem map_rotate' {α β : Type*} (f : α → β) : ∀ (l : List α) (n : ℕ),
    (l.rotate n).map f = (l.map f).rotate n := by
  intro l n
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons a l =>
      rw [List.rotate_cons_succ, List.map_cons, List.rotate_cons_succ, ih, List.map_append]
      rfl

/-- Negating a mask turns its `false` entries into selected ones. -/
private theorem count_true_map_not : ∀ l : List Bool, (l.map not).count true = l.count false := by
  intro l
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ih]

/-- A contract colouring only depends on the edge closure of its contract. -/
private theorem ccColoring_congr {D : Type*} {G : Hypermap D} {cc cc' : List D}
    {k : D → Color} (h : (G.insertE cc).Perm (G.insertE cc')) (hk : G.CcColoring cc k) :
    G.CcColoring cc' k :=
  ⟨fun x => (hk.edge x).trans h.mem_iff, hk.face⟩

/-- **The specification of `cfctr`**: every contract colouring of `cpmap cp` for
the contract selected by `mr` and `mc` gives a colouring of `cpmap cpc` whose
ring trace is the trace of the ring darts not erased by `mr`. -/
def CfctrSpec (cp : CProg) (mr mc : List Bool) (cpc : CProg) : Prop :=
  ∀ k : (cpmap cp).Dart → Color,
    (cpmap cp).map.CcColoring
        (listMask mr (cpmap cp).cpring ++ listMask mc (ctrenum cp)) k →
    ∃ k' : (cpmap cpc).Dart → Color, (cpmap cpc).map.Coloring k'
      ∧ (cpmap cpc).cpring.map k' = (listMask (mr.map not) (cpmap cp).cpring).map k

/-- Mapping over the ring of a rotation step. -/
private theorem map_cpring_R (n : ℕ) (cp : CProg) (f : (cpmap cp).Dart → Color) :
    (cpmap (.R n :: cp)).cpring.map f = ((cpmap cp).cpring.map f).rotate n := by
  have h : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
    Hypermap.cpring_ecpR (G := (cpmap cp).map) (x₀ := (cpmap cp).point) n
  rw [h]
  exact map_rotate' f (cpmap cp).cpring n

/-- Selecting from the ring of a rotation step. -/
private theorem listMask_cpring_R (n : ℕ) (cp : CProg) (m : List Bool)
    (hlen : m.length = (cpmap cp).cpring.length) :
    listMask (m.rotate n) (cpmap (.R n :: cp)).cpring
      = (listMask m (cpmap cp).cpring).rotate ((m.take (n % m.length)).count true) := by
  have h : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
    Hypermap.cpring_ecpR (G := (cpmap cp).map) (x₀ := (cpmap cp).point) n
  rw [h]
  exact listMask_rotate m (cpmap cp).cpring hlen n

/-- **The `R` step of `cfctr_correct`**: a rotation step only rotates the ring
and the mask. -/
private theorem cfctrSpec_R {cp : CProg} (i j : ℕ) {mr m' mc : List Bool} {cpc : CProg}
    (hm' : m'.rotate i = mr) (hlen : m'.length = (cpmap cp).cpring.length)
    (hj : j = (m'.take (i % m'.length)).count false)
    (hrec : CfctrSpec cp m' mc cpc) :
    CfctrSpec (.R i :: cp) mr mc (.R j :: cpc) := by
  intro k hk
  have hringR : (cpmap (.R i :: cp)).cpring = (cpmap cp).cpring.rotate i :=
    Hypermap.cpring_ecpR (G := (cpmap cp).map) (x₀ := (cpmap cp).point) i
  have hperm : (listMask mr ((cpmap cp).cpring.rotate i)).Perm
      (listMask m' (cpmap cp).cpring) := by
    rw [← hm']
    exact listMask_rotate_perm m' (cpmap cp).cpring hlen i
  have hk2 : (cpmap cp).map.CcColoring
      (listMask m' (cpmap cp).cpring ++ listMask mc (ctrenum cp)) k := by
    rw [ctrenum_R, hringR] at hk
    exact ccColoring_congr (insertE_perm (cpmap cp).map (hperm.append_right _)) hk
  obtain ⟨k', hk'col, hk'ring⟩ := hrec k hk2
  refine ⟨k', hk'col, ?_⟩
  have hnotlen : (m'.map not).length = m'.length := List.length_map ..
  have hj' : ((m'.map not).take (i % (m'.map not).length)).count true = j := by
    rw [hnotlen, ← List.map_take, count_true_map_not, hj]
  have hmrnot : mr.map not = (m'.map not).rotate i := by
    rw [← hm']
    exact map_rotate' not m' i
  have hL : (cpmap (.R j :: cpc)).cpring.map k'
      = ((listMask (m'.map not) (cpmap cp).cpring).map k).rotate j := by
    rw [map_cpring_R j cpc k', hk'ring]
    rfl
  have hR : (listMask (mr.map not) (cpmap (.R i :: cp)).cpring).map k
      = ((listMask (m'.map not) (cpmap cp).cpring).map k).rotate j := by
    rw [hmrnot, listMask_cpring_R i cp (m'.map not) (by rw [hnotlen]; exact hlen), hj']
    exact map_rotate' k _ j
  exact hL.trans hR.symm


/-! #### Extending a colouring along a construction step

Each construction step embeds the map below by an injection `f` that preserves
faces.  A colouring `h'` of the map below therefore determines a colouring of
the step map: an old face keeps its colour, and any face that the step creates
is given a fallback colour, chosen in each case so that the result is again a
colouring. -/

open scoped Classical in
/-- The colouring of a step map induced by a colouring of the map below: a dart
on the face of an old dart takes that dart's colour, and every other dart takes
the fallback colour `c`. -/
noncomputable def extColoring {D D' : Type*} (G' : Hypermap D') (f : D → D')
    (h' : D → Color) (c : Color) : D' → Color :=
  fun u => if hu : ∃ x, G'.CFace u (f x) then h' hu.choose else c

/-- The extended colouring is constant on faces. -/
theorem extColoring_congr {D D' : Type*} {G' : Hypermap D'} {f : D → D'} {h' : D → Color}
    {c : Color} (hf : ∀ x y, G'.CFace (f x) (f y) → h' x = h' y) {u v : D'}
    (huv : G'.CFace u v) : extColoring G' f h' c u = extColoring G' f h' c v := by
  classical
  by_cases hu : ∃ x, G'.CFace u (f x)
  · have hv : ∃ x, G'.CFace v (f x) := ⟨hu.choose, huv.symm.trans hu.choose_spec⟩
    rw [extColoring, extColoring, dite_eq_left hu, dite_eq_left hv]
    exact hf _ _ ((hu.choose_spec.symm.trans huv).trans hv.choose_spec)
  · have hv : ¬ ∃ x, G'.CFace v (f x) := fun hx => hu ⟨hx.choose, huv.trans hx.choose_spec⟩
    rw [extColoring, extColoring, dite_eq_right hu, dite_eq_right hv]

/-- The extended colouring agrees with the old one on old darts. -/
theorem extColoring_apply {D D' : Type*} {G : Hypermap D} {G' : Hypermap D'} {f : D → D'}
    {h' : D → Color} {c : Color} (hface : ∀ x y, G'.CFace (f x) (f y) ↔ G.CFace x y)
    (hh' : ∀ x, h' (G.face x) = h' x) (x : D) : extColoring G' f h' c (f x) = h' x := by
  classical
  have hu : ∃ y, G'.CFace (f x) (f y) := ⟨x, Equiv.Perm.SameCycle.refl _ _⟩
  rw [extColoring, dite_eq_left hu]
  exact (congr_of_sameCycle hh' ((hface x hu.choose).mp hu.choose_spec)).symm

/-- Off the image, the extended colouring is the fallback colour. -/
theorem extColoring_eq_of_not {D D' : Type*} {G' : Hypermap D'} {f : D → D'} {h' : D → Color}
    {c : Color} {u : D'} (hu : ¬ ∃ x, G'.CFace u (f x)) : extColoring G' f h' c u = c := by
  classical
  rw [extColoring, dite_eq_right hu]

/-- **The extended colouring is a colouring**, provided the faces it creates are
correctly coloured by the fallback. -/
theorem coloring_extColoring {D D' : Type*} {G : Hypermap D} {G' : Hypermap D'}
    {f : D → D'} {h' : D → Color} {c : Color} {Q : D' → Prop}
    (hface : ∀ x y, G'.CFace (f x) (f y) ↔ G.CFace x y)
    (hadj : ∀ x y, G'.Adj (f x) (f y) → G.Adj x y)
    (hcol : G.Coloring h')
    (hcover : ∀ u : D', (∃ x, G'.CFace u (f x)) ∨ Q u)
    (hnew : ∀ u : D', Q u → extColoring G' f h' c (G'.edge u) ≠ extColoring G' f h' c u)
    (hnew' : ∀ u : D', Q (G'.edge u) →
      extColoring G' f h' c (G'.edge u) ≠ extColoring G' f h' c u) :
    G'.Coloring (extColoring G' f h' c) := by
  have hcc : ∀ x y, G'.CFace (f x) (f y) → h' x = h' y :=
    fun x y hxy => hcol.cface ((hface x y).mp hxy)
  refine ⟨?_, fun u => extColoring_congr hcc (G'.cface_face u).symm⟩
  intro u
  rcases hcover u with ⟨x, hx⟩ | hQu
  · rcases hcover (G'.edge u) with ⟨y, hy⟩ | hQe
    · rw [extColoring_congr hcc hx, extColoring_congr hcc hy,
        extColoring_apply hface hcol.face x, extColoring_apply hface hcol.face y]
      have hadj' : G'.Adj (f x) (f y) := by
        have h0 : G'.Adj u (G'.edge u) := G'.adj_edge u
        rw [G'.adj_congr_left hx, G'.adj_congr_right hy] at h0
        exact h0
      obtain ⟨z, hz, hzy⟩ := hadj x y hadj'
      rw [hcol.cface hz, ← hcol.cface hzy]
      exact hcol.edge z
    · exact hnew' u hQe
  · exact hnew u hQu

/-! #### Walking along the ring of a contract colouring

If every ring dart selected by the contract mask has its E-link contracted, the
colour of the ring is constant along the selected stretch; so the first dart the
mask does *not* select has the same colour as the head of the ring. -/

/-- The first ring dart a mask leaves has the colour of the head of the ring,
provided every selected dart before it has its E-link contracted. -/
private theorem head_listMask_not {D : Type*} [Finite D] {G : Hypermap D} {h : D → Color}
    (hF : ∀ x, h (G.face x) = h x) :
    ∀ (m : List Bool) (x : D) (p : List D),
      List.IsChain (fun u v => u = G.node v) (x :: p) →
      (∀ y ∈ listMask m (x :: p), h (G.edge y) = h y) →
      ∀ z l', listMask (m.map not) (x :: p) = z :: l' → h z = h x := by
  intro m
  induction m with
  | nil =>
    intro x p _ _ z l' hz
    rw [List.map_nil, listMask_nil_mask] at hz
    exact absurd hz (by simp)
  | cons b m ih =>
    intro x p hchain hedge z l' hz
    cases b with
    | false =>
      rw [List.map_cons, show (!false) = true from rfl, listMask_true] at hz
      rw [(List.cons.injEq _ _ _ _).mp hz |>.1]
    | true =>
      cases p with
      | nil =>
        rw [List.map_cons, show (!true) = false from rfl, listMask_false,
          listMask_nil_list] at hz
        exact absurd hz (by simp)
      | cons y p =>
        have hxy : x = G.node y := (List.isChain_cons_cons.mp hchain).1
        have hchain' : List.IsChain (fun u v => u = G.node v) (y :: p) :=
          (List.isChain_cons_cons.mp hchain).2
        have hex : h (G.edge x) = h x := hedge x (by rw [listMask_true]; exact List.Mem.head _)
        have hy : h y = h x := by
          have h1 : G.face (G.edge x) = y := by
            rw [Hypermap.face_edge, hxy, Hypermap.inv_node_node]
          rw [← h1, hF, hex]
        rw [List.map_cons, show (!true) = false from rfl, listMask_false] at hz
        rw [ih y p hchain' (fun w hw => hedge w (by rw [listMask_true]; exact List.Mem.tail _ hw))
          z l' hz, hy]

/-! #### The recursive contract colouring of a `Y` step -/

/-- Swapping the first two blocks of a threefold concatenation. -/
private theorem perm_append_swap {α : Type*} (l₁ l₂ l₃ : List α) :
    ((l₁ ++ l₂) ++ l₃).Perm (l₂ ++ (l₁ ++ l₃)) := by
  rw [← List.append_assoc l₂ l₁ l₃]
  exact List.perm_append_comm.append_right l₃

/-- Membership in an image list. -/
private theorem mem_map_injcpStep {s : CpStep} {cp : CProg} {L : List (cpmap cp).Dart}
    {x : (cpmap cp).Dart} : injcpStep s cp x ∈ L.map (injcpStep s cp) ↔ x ∈ L := by
  constructor
  · intro hm
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    rwa [injcpStep_injective s cp hxy] at hy
  · intro hx
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

/-- No old dart lies in the edge closure of the two new ring darts of a `Y`
step. -/
private theorem notMem_insertE_new_Y (cp : CProg) (m : List Bool) (x : (cpmap cp).Dart) :
    injcpStep .Y cp x ∉ (cpmap (.Y :: cp)).map.insertE
      (listMask m [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point,
        (cpmap (.Y :: cp)).point]) := by
  intro hmem
  have hsub : ∀ y ∈ listMask m [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point,
      (cpmap (.Y :: cp)).point], y ∈ [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point,
      (cpmap (.Y :: cp)).point] := fun y hy => mem_of_mem_listMask _ _ hy
  have h1 := insertE_mono (cpmap (.Y :: cp)).map hsub hmem
  have hkey : (cpmap (.Y :: cp)).map.insertE
      [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point]
      = ([EcpDart.icp EcpDart.Xe, EcpDart.icp EcpDart.X, EcpDart.X, EcpDart.Xe] :
          List (cpmap (.Y :: cp)).Dart) := by
    rw [Hypermap.insertE_cons, Hypermap.insertE_cons, Hypermap.insertE_nil,
      show (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point
        = (EcpDart.icp EcpDart.Xe : (cpmap (.Y :: cp)).Dart) from
        PointedMap.node_ecpY (cpmap cp)]
    rfl
  rw [hkey] at h1
  exact icpY_notMem_new (cpmap cp) x h1

/-- **The recursive contract colouring of a `Y` step**: composing with the dart
injection turns a contract colouring of the step map into a contract colouring
of the map below, for the mask the recursive call of `cfctr` uses. -/
private theorem ccColoring_injcpY {cp : CProg} (hne : cp ≠ [])
    (b₁ b₂ b₃ : Bool) (mr' mc' : List Bool)
    {k : (cpmap (.Y :: cp)).Dart → Color} {h : (cpmap cp).Dart → Color}
    (hh : ∀ x, h x = k (injcpStep .Y cp x))
    (hk : (cpmap (.Y :: cp)).map.CcColoring
       (listMask (b₁ :: b₂ :: mr') (cpmap (.Y :: cp)).cpring
        ++ listMask (b₃ :: mc') (ctrenum (.Y :: cp))) k) :
    (cpmap cp).map.CcColoring
      (listMask (b₃ :: mr') (cpmap cp).cpring ++ listMask mc' (ctrenum cp)) h := by
  have hhead : (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).cpring.tail :=
    Hypermap.head_cpring
  have hMring : (cpmap (.Y :: cp)).cpring
      = (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point :: (cpmap (.Y :: cp)).point
        :: ((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp) :=
    PointedMap.cpring_ecpY' (cpmap cp)
  have hP : listMask (b₁ :: b₂ :: mr') (cpmap (.Y :: cp)).cpring
      = listMask [b₁, b₂]
          [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point]
        ++ (listMask mr' (cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp) := by
    rw [hMring, ← listMask_map]
    exact listMask_append [b₁, b₂]
      [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point] rfl mr'
      (((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp))
  have hQ : listMask (b₃ :: mc') (ctrenum (.Y :: cp))
      = (listMask (b₃ :: mc')
          ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp)).map (injcpStep CpStep.Y cp) := by
    rw [ctrenum_Y' cp hne, listMask_map]
  have hR : listMask (b₃ :: mr') (cpmap cp).cpring
      = listMask [b₃] [(cpmap cp).map.node (cpmap cp).point]
        ++ listMask mr' (cpmap cp).cpring.tail := by
    conv_lhs => rw [hhead]
    exact listMask_append [b₃] [(cpmap cp).map.node (cpmap cp).point] rfl mr'
      (cpmap cp).cpring.tail
  have hS : listMask (b₃ :: mc') ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp)
      = listMask [b₃] [(cpmap cp).map.node (cpmap cp).point]
        ++ listMask mc' (ctrenum cp) :=
    listMask_append [b₃] [(cpmap cp).map.node (cpmap cp).point] rfl mc' (ctrenum cp)
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hh, hh, congrArg k (edge_injcpStep (s := CpStep.Y) trivial cp x), hk.edge]
    have hL : injcpStep CpStep.Y cp x ∈ (cpmap (.Y :: cp)).map.insertE
          (listMask (b₁ :: b₂ :: mr') (cpmap (.Y :: cp)).cpring
            ++ listMask (b₃ :: mc') (ctrenum (.Y :: cp)))
        ↔ x ∈ (cpmap cp).map.insertE
            (listMask mr' (cpmap cp).cpring.tail
              ++ listMask (b₃ :: mc')
                  ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp)) := by
      rw [hP, hQ, Hypermap.insertE_append, Hypermap.insertE_append,
        insertE_map (cpmap cp).map (cpmap (.Y :: cp)).map (injcpStep CpStep.Y cp)
          (fun _ => rfl) (listMask mr' (cpmap cp).cpring.tail),
        insertE_map (cpmap cp).map (cpmap (.Y :: cp)).map (injcpStep CpStep.Y cp)
          (fun _ => rfl) (listMask (b₃ :: mc')
            ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp)),
        List.append_assoc, ← List.map_append, ← Hypermap.insertE_append, List.mem_append]
      constructor
      · rintro (hm | hm)
        · exact absurd hm (notMem_insertE_new_Y cp [b₁, b₂] x)
        · exact mem_map_injcpStep.mp hm
      · intro hm
        exact Or.inr (mem_map_injcpStep.mpr hm)
    have hG : x ∈ (cpmap cp).map.insertE
          (listMask (b₃ :: mr') (cpmap cp).cpring ++ listMask mc' (ctrenum cp))
        ↔ x ∈ (cpmap cp).map.insertE
            (listMask mr' (cpmap cp).cpring.tail
              ++ listMask (b₃ :: mc')
                  ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp)) := by
      rw [hR, hS]
      exact (insertE_perm (cpmap cp).map (perm_append_swap _ _ _)).mem_iff
    exact hL.trans hG.symm
  · rw [hh, hh]
    exact congr_of_sameCycle hk.face
      ((cface_injcpY cp _ _).mpr ((cpmap cp).map.cface_face x).symm)

/-! #### The recursive contract colouring of an `H` step -/

/-- No old dart of an `H` step lies in the edge closure of a list of new
darts. -/
private theorem notMem_insertE_newH (cp : CProg) (hp : (cpmap cp).Proper)
    (L : List (cpmap (.H :: cp)).Dart)
    (hL : ∀ y ∈ L, y ∈ [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
      (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point])
    (x : (cpmap cp).Dart) :
    injcpStep .H cp x ∉ (cpmap (.H :: cp)).map.insertE L := by
  intro hmem
  have h1 := insertE_mono (cpmap (.H :: cp)).map hL hmem
  have hkey : (cpmap (.H :: cp)).map.insertE
      [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point,
        (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point]
      = ([EcpDart.icp (EcpDart.icp EcpDart.Xe), EcpDart.icp (EcpDart.icp EcpDart.X),
          EcpDart.X, EcpDart.Xe, EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] :
          List (cpmap (.H :: cp)).Dart) := by
    rw [Hypermap.insertE_cons, Hypermap.insertE_cons, Hypermap.insertE_cons,
      Hypermap.insertE_nil,
      show (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
        = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : (cpmap (.H :: cp)).Dart) from
        PointedMap.node_ecpH (cpmap cp) hp]
    rfl
  rw [hkey] at h1
  exact icpH_notMem_new (cpmap cp) x h1

/-- No new dart of an `H` step lies in an image list. -/
private theorem notMem_map_injcpH_new (cp : CProg) (L : List (cpmap cp).Dart)
    {u : (cpmap (.H :: cp)).Dart}
    (hu : u ∈ ([EcpDart.icp (EcpDart.icp EcpDart.Xe), EcpDart.icp (EcpDart.icp EcpDart.X),
      EcpDart.X, EcpDart.Xe, EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] :
      List (cpmap (.H :: cp)).Dart)) : u ∉ L.map (injcpStep .H cp) := by
  intro hm
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hm
  exact icpH_notMem_new (cpmap cp) x hu

/-- **The recursive contract colouring of an `H` step**: composing with the dart
injection turns a contract colouring of the step map into a contract colouring
of the map below, for the mask the recursive call of `cfctr` uses. -/
private theorem ccColoring_injcpH {cp : CProg} (hp : (cpmap cp).Proper)
    (b₁ b₂ b₃ b₄ b₅ : Bool) (mr' mc' : List Bool)
    {k : (cpmap (.H :: cp)).Dart → Color} {h : (cpmap cp).Dart → Color}
    (hh : ∀ x, h x = k (injcpStep .H cp x))
    (hk : (cpmap (.H :: cp)).map.CcColoring
       (listMask (b₁ :: b₂ :: mr') (cpmap (.H :: cp)).cpring
        ++ listMask (b₃ :: b₄ :: b₅ :: mc') (ctrenum (.H :: cp))) k) :
    (cpmap cp).map.CcColoring
      (listMask (b₄ :: b₅ :: mr') (cpmap cp).cpring ++ listMask mc' (ctrenum cp)) h := by
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hP : listMask (b₁ :: b₂ :: mr') (cpmap (.H :: cp)).cpring
      = listMask [b₁, b₂]
          [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point]
        ++ (listMask mr' ((cpmap cp).cpring.drop 2)).map (injcpStep CpStep.H cp) := by
    rw [hMring, ← listMask_map]
    exact listMask_append [b₁, b₂]
      [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point] rfl mr'
      (((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp))
  have hQ : listMask (b₃ :: b₄ :: b₅ :: mc') (ctrenum (.H :: cp))
      = listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point]
        ++ (listMask (b₄ :: b₅ :: mc')
            ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
              :: ctrenum cp)).map (injcpStep CpStep.H cp) := by
    rw [ctrenum_H, ← listMask_map]
    exact listMask_append [b₃]
      [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point] rfl (b₄ :: b₅ :: mc')
      ((((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
          :: ctrenum cp)).map (injcpStep CpStep.H cp))
  have hR : listMask (b₄ :: b₅ :: mr') (cpmap cp).cpring
      = listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point]
        ++ listMask mr' ((cpmap cp).cpring.drop 2) := by
    conv_lhs => rw [hGprop]
    exact listMask_append [b₄, b₅]
      [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point] rfl mr'
      ((cpmap cp).cpring.drop 2)
  have hS : listMask (b₄ :: b₅ :: mc')
        ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: ctrenum cp)
      = listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point]
        ++ listMask mc' (ctrenum cp) :=
    listMask_append [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point] rfl mc'
      (ctrenum cp)
  have hsub1 : ∀ y ∈ listMask [b₁, b₂]
      [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point],
      y ∈ [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point,
        (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point] := by
    intro y hy
    have hy2 := mem_of_mem_listMask [b₁, b₂] _ hy
    rcases List.mem_cons.mp hy2 with rfl | hy3
    · exact List.Mem.head _
    · rcases List.mem_cons.mp hy3 with rfl | hy4
      · exact List.Mem.tail _ (List.Mem.head _)
      · cases hy4
  have hsub2 : ∀ y ∈ listMask [b₃]
      [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point],
      y ∈ [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point,
        (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point] := by
    intro y hy
    have hy2 := mem_of_mem_listMask [b₃] _ hy
    rcases List.mem_cons.mp hy2 with rfl | hy3
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · cases hy3
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hh, hh, congrArg k (edge_injcpStep (s := CpStep.H) trivial cp x), hk.edge]
    have hL : injcpStep CpStep.H cp x ∈ (cpmap (.H :: cp)).map.insertE
          (listMask (b₁ :: b₂ :: mr') (cpmap (.H :: cp)).cpring
            ++ listMask (b₃ :: b₄ :: b₅ :: mc') (ctrenum (.H :: cp)))
        ↔ x ∈ (cpmap cp).map.insertE
            (listMask mr' ((cpmap cp).cpring.drop 2)
              ++ listMask (b₄ :: b₅ :: mc')
                  ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
                    :: ctrenum cp)) := by
      rw [hP, hQ, Hypermap.insertE_append, Hypermap.insertE_append, Hypermap.insertE_append,
        insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
          (fun _ => rfl) (listMask mr' ((cpmap cp).cpring.drop 2)),
        insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
          (fun _ => rfl) (listMask (b₄ :: b₅ :: mc')
            ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: ctrenum cp)),
        Hypermap.insertE_append]
      simp only [List.mem_append, mem_map_injcpStep]
      constructor
      · rintro ((hm | hm) | (hm | hm))
        · exact absurd hm (notMem_insertE_newH cp hp _ hsub1 x)
        · exact Or.inl hm
        · exact absurd hm (notMem_insertE_newH cp hp _ hsub2 x)
        · exact Or.inr hm
      · rintro (hm | hm)
        · exact Or.inl (Or.inr hm)
        · exact Or.inr (Or.inr hm)
    have hG : x ∈ (cpmap cp).map.insertE
          (listMask (b₄ :: b₅ :: mr') (cpmap cp).cpring ++ listMask mc' (ctrenum cp))
        ↔ x ∈ (cpmap cp).map.insertE
            (listMask mr' ((cpmap cp).cpring.drop 2)
              ++ listMask (b₄ :: b₅ :: mc')
                  ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
                    :: ctrenum cp)) := by
      rw [hR, hS]
      exact (insertE_perm (cpmap cp).map (perm_append_swap _ _ _)).mem_iff
    exact hL.trans hG.symm
  · rw [hh, hh]
    exact congr_of_sameCycle hk.face
      ((cface_injcpH cp _ _).mpr ((cpmap cp).map.cface_face x).symm)

/-- After a `Y` step the new dart lies on the face of the edge of its node. -/
private theorem cface_edge_node_ecpY (M : PointedMap) :
    M.ecpY.map.CFace M.ecpY.point (M.ecpY.map.edge (M.ecpY.map.node M.ecpY.point)) := by
  rw [show M.ecpY.map.node M.ecpY.point = (EcpDart.icp EcpDart.Xe : M.ecpY.Dart) from
    PointedMap.node_ecpY M]
  exact (PointedMap.cface_ecpY M _).mpr (Or.inr rfl)

/-- **The `Y` step of `cfctr_correct`, contracted ring edge**: when the contract
erases one of the two outer ring edges of the step, the step disappears and the
colouring of the contracted map is unchanged. -/
private theorem cfctrSpec_Y_erase {cp : CProg} (hne : cp ≠ []) {b₁ b₂ : Bool}
    (hb : (b₁ = true ∧ b₂ = false) ∨ (b₁ = false ∧ b₂ = true))
    (mr' mc' : List Bool) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (false :: mr') mc' cpc₀) :
    CfctrSpec (.Y :: cp) (b₁ :: b₂ :: mr') (false :: mc') cpc₀ := by
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .Y cp x) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨h', hcol', Eh⟩ := hrec h (ccColoring_injcpY hne b₁ b₂ false mr' mc' hh hk)
  refine ⟨h', hcol', ?_⟩
  have hhead : (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).cpring.tail := Hypermap.head_cpring
  have hMring : (cpmap (.Y :: cp)).cpring
      = (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point :: (cpmap (.Y :: cp)).point
        :: ((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp) :=
    PointedMap.cpring_ecpY' (cpmap cp)
  have hnG : k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
      = k (injcpStep CpStep.Y cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpY' (cpmap cp))
  have hEh : (listMask ((false :: mr').map not) (cpmap cp).cpring).map h
      = h ((cpmap cp).map.node (cpmap cp).point)
        :: (listMask (mr'.map not) (cpmap cp).cpring.tail).map h := by
    conv_lhs => rw [hhead]
    rfl
  have hT : (listMask ((b₁ :: b₂ :: mr').map not) (cpmap (.Y :: cp)).cpring).map k
      = (listMask [!b₁, !b₂]
            [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point]).map k
        ++ (listMask (mr'.map not) (cpmap cp).cpring.tail).map h := by
    rw [hMring,
      show ((b₁ :: b₂ :: mr').map not) = [!b₁, !b₂] ++ mr'.map not from rfl,
      show ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point :: (cpmap (.Y :: cp)).point
            :: (((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp)))
          = [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point]
            ++ (((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp)) from rfl,
      listMask_append [!b₁, !b₂]
        [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point] rfl
        (mr'.map not) (((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp)),
      List.map_append, listMask_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun x _ => (hh x).symm)
  have hhd : (listMask [!b₁, !b₂]
        [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point]).map k
      = [h ((cpmap cp).map.node (cpmap cp).point)] := by
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmem : (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point
          ∈ (cpmap (.Y :: cp)).map.insertE
            (listMask (true :: false :: mr') (cpmap (.Y :: cp)).cpring
              ++ listMask (false :: mc') (ctrenum (.Y :: cp))) := by
        refine mem_insertE_self _ (List.mem_append_left _ ?_)
        rw [hMring]
        exact List.Mem.head _
      have hE := (hk.edge _).mpr hmem
      have hX : k (cpmap (.Y :: cp)).point
          = k ((cpmap (.Y :: cp)).map.edge
              ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)) :=
        congr_of_sameCycle hk.face (cface_edge_node_ecpY (cpmap cp))
      rw [show (listMask [!true, !false]
            [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point])
          = [(cpmap (.Y :: cp)).point] from rfl, List.map_cons, List.map_nil, hh,
        ← hnG, ← hE, ← hX]
    · rw [show (listMask [!false, !true]
            [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point, (cpmap (.Y :: cp)).point])
          = [(cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point] from rfl,
        List.map_cons, List.map_nil, hh, ← hnG]
  rw [Eh, hEh, hT, hhd]
  rfl

/-- No new dart of a `Y` step lies in an image list. -/
private theorem notMem_map_injcpY_new (cp : CProg) (L : List (cpmap cp).Dart)
    {u : (cpmap (.Y :: cp)).Dart}
    (hu : u ∈ ([EcpDart.icp EcpDart.Xe, EcpDart.icp EcpDart.X, EcpDart.X, EcpDart.Xe] :
      List (cpmap (.Y :: cp)).Dart)) : u ∉ L.map (injcpStep .Y cp) := by
  intro hm
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hm
  exact icpY_notMem_new (cpmap cp) x hu

/-- **The `Y` step of `cfctr_correct`, contracted foot**: when the contract
erases the foot of the `Y` but neither of its outer ring edges, the new face is
cut off from the ring and the step becomes a `U` step. -/
private theorem cfctrSpec_Y_U {cp : CProg} (hne : cp ≠ []) (mr' mc' : List Bool)
    {cpc₀ : CProg} (hrec : CfctrSpec cp (true :: mr') mc' cpc₀) :
    CfctrSpec (.Y :: cp) (false :: false :: mr') (true :: mc') (.U :: cpc₀) := by
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .Y cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpY hne false false true mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  have hhead : (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).cpring.tail := Hypermap.head_cpring
  have hMring : (cpmap (.Y :: cp)).cpring
      = (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point :: (cpmap (.Y :: cp)).point
        :: ((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp) :=
    PointedMap.cpring_ecpY' (cpmap cp)
  have hEh : (listMask ((true :: mr').map not) (cpmap cp).cpring).map h
      = (listMask (mr'.map not) (cpmap cp).cpring.tail).map h := by
    conv_lhs => rw [hhead]
    rfl
  rw [hEh] at Eh
  -- walking along the erased stretch of the ring
  have hEr : ∀ y ∈ listMask (true :: mr') (cpmap cp).cpring,
      h ((cpmap cp).map.edge y) = h y := fun y hy =>
    (hcc.edge y).mpr (mem_insertE_self _ (List.mem_append_left _ hy))
  have hchain : List.IsChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).cpring.tail) := by
    have h0 : List.IsChain (fun u v => u = (cpmap cp).map.node v) (cpmap cp).cpring :=
      (Hypermap.isCyclicChain_cpring (G := (cpmap cp).map) (x₀ := (cpmap cp).point)).isChain
    rw [hhead] at h0
    exact h0
  obtain ⟨z, l', hzl⟩ : ∃ z l', listMask (mr'.map not) (cpmap cp).cpring.tail = z :: l' := by
    match hm : listMask (mr'.map not) (cpmap cp).cpring.tail with
    | z :: l' => exact ⟨z, l', rfl⟩
    | [] =>
      exfalso
      rw [hm, List.map_nil] at Eh
      refine Hypermap.cpring_ne_nil (G := (cpmap cpc₀).map) (x₀ := (cpmap cpc₀).point) ?_
      rcases hcpr : (cpmap cpc₀).cpring with _ | ⟨a, t⟩
      · exact hcpr
      · rw [hcpr] at Eh; simp at Eh
  have hwalk : h z = h ((cpmap cp).map.node (cpmap cp).point) := by
    refine head_listMask_not hcc.face (true :: mr') _ _ hchain
      (fun y hy => hEr y (by rw [hhead]; exact hy)) z l' hzl
  have hGcring : (cpmap cpc₀).cpring
      = (cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).cpring.tail :=
    Hypermap.head_cpring
  have h'nGc : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
      = h ((cpmap cp).map.node (cpmap cp).point) := by
    have h2 := Eh
    rw [hGcring, hzl] at h2
    rw [List.map_cons, List.map_cons] at h2
    injection h2 with h3 _
    rw [h3, hwalk]
  -- the colour of the new face of the `Y` step
  have hnG : k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
      = k (injcpStep CpStep.Y cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpY' (cpmap cp))
  have hX : k (cpmap (.Y :: cp)).point
      = k ((cpmap (.Y :: cp)).map.edge
          ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpY (cpmap cp))
  have hccM : listMask (false :: false :: mr') (cpmap (.Y :: cp)).cpring
        ++ listMask (true :: mc') (ctrenum (.Y :: cp))
      = (listMask mr' (cpmap cp).cpring.tail
          ++ listMask (true :: mc')
              ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp)).map
            (injcpStep CpStep.Y cp) := by
    rw [hMring, ctrenum_Y' cp hne, listMask_false, listMask_false, listMask_map,
      listMask_map, List.map_append]
  have hnXX : k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
      ≠ k (cpmap (.Y :: cp)).point := by
    intro hcontra
    have h1 : k ((cpmap (.Y :: cp)).map.edge
        ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point))
        = k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point) := by
      rw [← hX, ← hcontra]
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.Y :: cp)).map (injcpStep CpStep.Y cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpY_new cp _ ?_ h2
    rw [show (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point
      = (EcpDart.icp EcpDart.Xe : (cpmap (.Y :: cp)).Dart) from PointedMap.node_ecpY (cpmap cp)]
    exact List.Mem.head _
  -- the colouring of the `U` step
  have hface : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.U :: cpc₀)).map.CFace (injcpStep .U cpc₀ x) (injcpStep .U cpc₀ y)
        ↔ (cpmap cpc₀).map.CFace x y :=
    fun x y => Hypermap.cface_icpU (cpmap cpc₀).map (cpmap cpc₀).point x y
  have hcc' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.U :: cpc₀)).map.CFace (injcpStep .U cpc₀ x) (injcpStep .U cpc₀ y)
        → h' x = h' y := fun x y hxy => hcol'.cface ((hface x y).mp hxy)
  have hk'X : extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.Y :: cp)).point) (cpmap (.U :: cpc₀)).point
      = k (cpmap (.Y :: cp)).point := by
    refine extColoring_eq_of_not ?_
    rintro ⟨x, hx⟩
    have hxx : (EcpDart.icp x : EcpDart (cpmap cpc₀).Dart) = EcpDart.X :=
      (Hypermap.cface_ecpU (cpmap cpc₀).map (cpmap cpc₀).point _).mp hx
    exact absurd hxx (by simp)
  have hk'Xe : extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.Y :: cp)).point)
        ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
      = h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) := by
    have hface1 : (cpmap (.U :: cpc₀)).map.CFace
        ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
        (injcpStep .U cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point)) :=
      (Hypermap.cface_Xe_icpU (cpmap cpc₀).map (cpmap cpc₀).point
        ((cpmap cpc₀).map.node (cpmap cpc₀).point)).mpr (Equiv.Perm.SameCycle.refl _ _)
    rw [extColoring_congr hcc' hface1]
    exact extColoring_apply hface hcol'.face _
  have hk'ne : extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.Y :: cp)).point)
        ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
      ≠ extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.Y :: cp)).point) (cpmap (.U :: cpc₀)).point := by
    rw [hk'Xe, hk'X, h'nGc, hh, ← hnG]
    exact hnXX
  refine ⟨extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
    (k (cpmap (.Y :: cp)).point), ?_, ?_⟩
  · refine coloring_extColoring hface
      (fun x y hxy => (Hypermap.adj_icpU (cpmap cpc₀).map (cpmap cpc₀).point x y).mp hxy)
      hcol' (fun u => Hypermap.fband_icpU (cpmap cpc₀).map (cpmap cpc₀).point u) ?_ ?_
    · intro u hu
      obtain rfl : u = (cpmap (.U :: cpc₀)).point :=
        (Hypermap.cface_ecpU (cpmap cpc₀).map (cpmap cpc₀).point u).mp hu
      exact hk'ne
    · intro u hu
      have hu2 : (cpmap (.U :: cpc₀)).map.edge u = (cpmap (.U :: cpc₀)).point :=
        (Hypermap.cface_ecpU (cpmap cpc₀).map (cpmap cpc₀).point _).mp hu
      have hu3 : u = (cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point := by
        have h4 : (cpmap (.U :: cpc₀)).map.edge
            ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
            = (cpmap (.U :: cpc₀)).point := rfl
        exact (cpmap (.U :: cpc₀)).map.edge.injective (hu2.trans h4.symm)
      rw [hu3] at hu2
      rw [hu3, hu2, hk'X, hk'Xe, h'nGc, hh, ← hnG]
      exact fun hcon => hnXX hcon.symm
  · have hNring : (cpmap (.U :: cpc₀)).cpring
        = (cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point
          :: (cpmap (.U :: cpc₀)).point
          :: (cpmap cpc₀).cpring.map (injcpStep .U cpc₀) :=
      PointedMap.cpring_ecpU' (cpmap cpc₀)
    have hT : (listMask ((false :: false :: mr').map not) (cpmap (.Y :: cp)).cpring).map k
        = k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
          :: k (cpmap (.Y :: cp)).point
          :: (listMask (mr'.map not) (cpmap cp).cpring.tail).map h := by
      rw [hMring, show ((false :: false :: mr').map not) = true :: true :: mr'.map not from rfl,
        listMask_true, listMask_true, listMask_map, List.map_cons, List.map_cons, List.map_map]
      congr 2
      exact List.map_congr_left (fun x _ => (hh x).symm)
    rw [hNring, hT, List.map_cons, List.map_cons, List.map_map, hk'Xe, hk'X, h'nGc, hh, ← hnG]
    congr 2
    rw [← Eh]
    exact List.map_congr_left (fun x _ => extColoring_apply hface hcol'.face x)

/-- **The `Y` step of `cfctr_correct`, untouched step**: when the contract meets
neither the outer ring edges nor the foot of the `Y`, the step survives. -/
private theorem cfctrSpec_Y_Y {cp : CProg} (hne : cp ≠ []) (hprop : (cpmap cp).Proper)
    (mr' mc' : List Bool) {cpc₀ : CProg} (hrec : CfctrSpec cp (false :: mr') mc' cpc₀) :
    CfctrSpec (.Y :: cp) (false :: false :: mr') (false :: mc') (.Y :: cpc₀) := by
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .Y cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpY hne false false false mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hprop
  have hhead : (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).cpring.tail := Hypermap.head_cpring
  have hGtail : (cpmap cp).cpring.tail = (cpmap cp).point :: (cpmap cp).cpring.drop 2 := by
    conv_lhs => rw [hGprop]
    rfl
  have hMring : (cpmap (.Y :: cp)).cpring
      = (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point :: (cpmap (.Y :: cp)).point
        :: ((cpmap cp).cpring.tail).map (injcpStep CpStep.Y cp) :=
    PointedMap.cpring_ecpY' (cpmap cp)
  have hEh : (listMask ((false :: mr').map not) (cpmap cp).cpring).map h
      = h ((cpmap cp).map.node (cpmap cp).point)
        :: (listMask (mr'.map not) (cpmap cp).cpring.tail).map h := by
    conv_lhs => rw [hhead]
    rfl
  rw [hEh] at Eh
  have hGcprop : (cpmap cpc₀).Proper := hcol'.properCpring (cpmap cpc₀).point
  have hGcring : (cpmap cpc₀).cpring
      = (cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).point
        :: (cpmap cpc₀).cpring.drop 2 := Hypermap.head_proper_cpring hGcprop
  obtain ⟨z, l', hzl⟩ : ∃ z l', listMask (mr'.map not) (cpmap cp).cpring.tail = z :: l' := by
    match hm : listMask (mr'.map not) (cpmap cp).cpring.tail with
    | z :: l' => exact ⟨z, l', rfl⟩
    | [] =>
      exfalso
      rw [hm, List.map_nil] at Eh
      rw [hGcring] at Eh
      simp at Eh
  have hsplit : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
        = h ((cpmap cp).map.node (cpmap cp).point)
      ∧ h' (cpmap cpc₀).point = h z
      ∧ ((cpmap cpc₀).cpring.drop 2).map h' = l'.map h := by
    have h2 := Eh
    rw [hGcring, hzl] at h2
    simp only [List.map_cons] at h2
    injection h2 with h3 h4
    injection h4 with h5 h6
    exact ⟨h3, h5, h6⟩
  have hEr : ∀ y ∈ listMask (false :: mr') (cpmap cp).cpring,
      h ((cpmap cp).map.edge y) = h y := fun y hy =>
    (hcc.edge y).mpr (mem_insertE_self _ (List.mem_append_left _ hy))
  have hchain2 : List.IsChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).point :: (cpmap cp).cpring.drop 2) := by
    have h0 : List.IsChain (fun u v => u = (cpmap cp).map.node v) (cpmap cp).cpring :=
      (Hypermap.isCyclicChain_cpring (G := (cpmap cp).map) (x₀ := (cpmap cp).point)).isChain
    rw [hGprop] at h0
    exact (List.isChain_cons_cons.mp h0).2
  have hwalk : h z = h (cpmap cp).point := by
    refine head_listMask_not hcc.face mr' _ _ hchain2 (fun y hy => hEr y ?_) z l' ?_
    · rw [hhead, hGtail]
      exact hy
    · rw [← hGtail]
      exact hzl
  have h'nGc : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
      = h ((cpmap cp).map.node (cpmap cp).point) := hsplit.1
  have h'Gc : h' (cpmap cpc₀).point = h (cpmap cp).point := hsplit.2.1.trans hwalk
  -- colours of the new face of the `Y` step below
  have hnG : k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
      = k (injcpStep CpStep.Y cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpY' (cpmap cp))
  have hX : k (cpmap (.Y :: cp)).point
      = k ((cpmap (.Y :: cp)).map.edge
          ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpY (cpmap cp))
  have hccM : listMask (false :: false :: mr') (cpmap (.Y :: cp)).cpring
        ++ listMask (false :: mc') (ctrenum (.Y :: cp))
      = (listMask mr' (cpmap cp).cpring.tail
          ++ listMask (false :: mc')
              ((cpmap cp).map.node (cpmap cp).point :: ctrenum cp)).map
            (injcpStep CpStep.Y cp) := by
    rw [hMring, ctrenum_Y' cp hne, listMask_false, listMask_false, listMask_map,
      listMask_map, List.map_append]
  have hnXX : k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
      ≠ k (cpmap (.Y :: cp)).point := by
    intro hcontra
    have h1 : k ((cpmap (.Y :: cp)).map.edge
        ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point))
        = k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point) := by
      rw [← hX, ← hcontra]
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.Y :: cp)).map (injcpStep CpStep.Y cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpY_new cp _ ?_ h2
    rw [show (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point
      = (EcpDart.icp EcpDart.Xe : (cpmap (.Y :: cp)).Dart) from PointedMap.node_ecpY (cpmap cp)]
    exact List.Mem.head _
  have hXe : (cpmap (.Y :: cp)).map.CFace
      ((cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point)
      (injcpStep .Y cp (cpmap cp).point) := by
    have h1 : (cpmap (.Y :: cp)).map.face ((cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point)
        = injcpStep .Y cp (cpmap cp).point := by
      rw [Hypermap.face_edge]
      exact Hypermap.node_inv_ecpY_X (cpmap cp).map (cpmap cp).point hprop
    rw [← h1]
    exact (cpmap (.Y :: cp)).map.cface_face _
  have hXne : k (injcpStep .Y cp (cpmap cp).point) ≠ k (cpmap (.Y :: cp)).point := by
    have hEq : k ((cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point)
        = k (injcpStep .Y cp (cpmap cp).point) := congr_of_sameCycle hk.face hXe
    intro hcontra
    have h1 : k ((cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point)
        = k (cpmap (.Y :: cp)).point := hEq.trans hcontra
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.Y :: cp)).map (injcpStep CpStep.Y cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpY_new cp _ ?_ h2
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  -- the colouring of the `Y` step above
  have hface' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (injcpStep .Y cpc₀ x) (injcpStep .Y cpc₀ y)
        ↔ (cpmap cpc₀).map.CFace x y := cface_injcpY cpc₀
  have hcc' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (injcpStep .Y cpc₀ x) (injcpStep .Y cpc₀ y)
        → h' x = h' y := fun x y hxy => hcol'.cface ((hface' x y).mp hxy)
  have hfaceX : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (cpmap (.Y :: cpc₀)).point u
        ↔ u = (cpmap (.Y :: cpc₀)).point
          ∨ u = (cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point :=
    fun u => PointedMap.cface_ecpY (cpmap cpc₀) u
  have hadjY : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.Adj (cpmap (.Y :: cpc₀)).point u
        ↔ (cpmap (.Y :: cpc₀)).map.CFace u
              (injcpStep .Y cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point))
          ∨ (cpmap (.Y :: cpc₀)).map.CFace u (injcpStep .Y cpc₀ (cpmap cpc₀).point) :=
    fun u => PointedMap.adj_ecpY (cpmap cpc₀) hGcprop u
  have hk'X : extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
        (k (cpmap (.Y :: cp)).point) (cpmap (.Y :: cpc₀)).point
      = k (cpmap (.Y :: cp)).point :=
    extColoring_eq_of_not (fun hx => not_cface_injcpY cpc₀ hx.choose hx.choose_spec)
  have hcfnode : (cpmap (.Y :: cpc₀)).map.CFace
      ((cpmap (.Y :: cpc₀)).map.node (cpmap (.Y :: cpc₀)).point)
      (injcpStep .Y cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point)) :=
    PointedMap.cface_node_ecpY' (cpmap cpc₀)
  have hk'nX : extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
        (k (cpmap (.Y :: cp)).point)
        ((cpmap (.Y :: cpc₀)).map.node (cpmap (.Y :: cpc₀)).point)
      = h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) := by
    rw [extColoring_congr hcc' hcfnode]
    exact extColoring_apply hface' hcol'.face _
  have hinv : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (cpmap (.Y :: cpc₀)).point
          ((cpmap (.Y :: cpc₀)).map.edge u)
        → (cpmap (.Y :: cpc₀)).map.edge ((cpmap (.Y :: cpc₀)).map.edge u) = u := by
    intro u hu
    rcases (hfaceX _).mp hu with he | he
    · have h1 : (cpmap (.Y :: cpc₀)).map.edge
          ((cpmap (.Y :: cpc₀)).map.edge (cpmap (.Y :: cpc₀)).point)
          = (cpmap (.Y :: cpc₀)).point := rfl
      have h2 : u = (cpmap (.Y :: cpc₀)).map.edge (cpmap (.Y :: cpc₀)).point :=
        (cpmap (.Y :: cpc₀)).map.edge.injective (he.trans h1.symm)
      rw [he, h2]
    · have h1 : (cpmap (.Y :: cpc₀)).map.edge
          ((cpmap (.Y :: cpc₀)).map.edge
            ((cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point))
          = (cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point := rfl
      have h2 : u = (cpmap (.Y :: cpc₀)).map.edge
          ((cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point) :=
        (cpmap (.Y :: cpc₀)).map.edge.injective (he.trans h1.symm)
      rw [he, h2]
  have hnew : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (cpmap (.Y :: cpc₀)).point u →
      extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
          (k (cpmap (.Y :: cp)).point) ((cpmap (.Y :: cpc₀)).map.edge u)
        ≠ extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
          (k (cpmap (.Y :: cp)).point) u := by
    intro u hu
    have hku : extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
        (k (cpmap (.Y :: cp)).point) u = k (cpmap (.Y :: cp)).point :=
      (extColoring_congr hcc' hu).symm.trans hk'X
    have hadjX : (cpmap (.Y :: cpc₀)).map.Adj (cpmap (.Y :: cpc₀)).point
        ((cpmap (.Y :: cpc₀)).map.edge u) :=
      ((cpmap (.Y :: cpc₀)).map.adj_congr_left hu _).mpr
        ((cpmap (.Y :: cpc₀)).map.adj_edge u)
    rw [hku]
    rcases (hadjY _).mp hadjX with hc | hc
    · rw [extColoring_congr hcc' hc, extColoring_apply hface' hcol'.face, h'nGc, hh, ← hnG]
      exact hnXX
    · rw [extColoring_congr hcc' hc, extColoring_apply hface' hcol'.face, h'Gc, hh]
      exact hXne
  refine ⟨extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
    (k (cpmap (.Y :: cp)).point), ?_, ?_⟩
  · refine coloring_extColoring hface'
      (fun x y hxy => (PointedMap.adj_icpY' (cpmap cpc₀) x y).mp hxy) hcol'
      (fun u => fband_injcpY cpc₀ u) hnew ?_
    intro u hu
    have h1 := hnew _ hu
    rw [hinv u hu] at h1
    exact fun hcon => h1 hcon.symm
  · have hNring : (cpmap (.Y :: cpc₀)).cpring
        = (cpmap (.Y :: cpc₀)).map.node (cpmap (.Y :: cpc₀)).point
          :: (cpmap (.Y :: cpc₀)).point
          :: ((cpmap cpc₀).cpring.tail).map (injcpStep CpStep.Y cpc₀) :=
      PointedMap.cpring_ecpY' (cpmap cpc₀)
    have hT : (listMask ((false :: false :: mr').map not) (cpmap (.Y :: cp)).cpring).map k
        = k ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
          :: k (cpmap (.Y :: cp)).point
          :: (listMask (mr'.map not) (cpmap cp).cpring.tail).map h := by
      rw [hMring, show ((false :: false :: mr').map not) = true :: true :: mr'.map not from rfl,
        listMask_true, listMask_true, listMask_map, List.map_cons, List.map_cons, List.map_map]
      congr 2
      exact List.map_congr_left (fun x _ => (hh x).symm)
    have hGctail : (cpmap cpc₀).cpring.tail
        = (cpmap cpc₀).point :: (cpmap cpc₀).cpring.drop 2 := by
      conv_lhs => rw [hGcring]
      rfl
    rw [hNring, hT]
    simp only [List.map_cons, List.map_map]
    rw [hk'nX, hk'X, h'nGc, hh, ← hnG, hGctail, hzl]
    simp only [List.map_cons, Function.comp_apply]
    congr 2
    rw [show (extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
          (k (cpmap (.Y :: cp)).point) ∘ injcpStep .Y cpc₀)
        = h' from funext (fun x => extColoring_apply hface' hcol'.face x),
      extColoring_apply hface' hcol'.face, h'Gc, hwalk, hsplit.2.2]

/-- **The `Y` base case of `cfctr_correct`**: the initial `Y` step builds the
three-dart ring from the single edge, and each of the four sparse contracts of
its ring is handled directly. -/
private theorem cfctrSpec_Y_nil (b₁ b₂ b₃ : Bool) (mc : List Bool)
    (hb : ¬ notSparse b₁ b₂ b₃ = true) :
    CfctrSpec [.Y] [b₁, b₂, b₃] mc (if b₁ || b₂ || b₃ then [] else [.Y]) := by
  have hG0ring : (cpmap ([] : CProg)).cpring
      = [(cpmap ([] : CProg)).map.node (cpmap ([] : CProg)).point,
          (cpmap ([] : CProg)).point] := PointedMap.cpring_cpmap0
  have hG0tail : (cpmap ([] : CProg)).cpring.tail = [(cpmap ([] : CProg)).point] := by
    rw [hG0ring]
    rfl
  have hMring : (cpmap [CpStep.Y]).cpring
      = (cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point :: (cpmap [CpStep.Y]).point
        :: ((cpmap ([] : CProg)).cpring.tail).map (injcpStep CpStep.Y []) :=
    PointedMap.cpring_ecpY' (cpmap [])
  have hM3 : (cpmap [CpStep.Y]).cpring
      = [(cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point, (cpmap [CpStep.Y]).point,
          injcpStep CpStep.Y [] (cpmap ([] : CProg)).point] := by
    rw [hMring, hG0tail]
    rfl
  have hface0 : ∀ b : (cpmap ([] : CProg)).Dart, (cpmap ([] : CProg)).map.face b = b :=
    fun _ => rfl
  cases b₁ <;> cases b₂ <;> cases b₃ <;> try exact absurd rfl hb
  -- (false, false, false): the step survives
  · change CfctrSpec [CpStep.Y] [false, false, false] mc [CpStep.Y]
    intro k hk
    refine ⟨k, ?_, ?_⟩
    · refine Hypermap.ccColoring_nil_iff.mp ?_
      have hcc : listMask [false, false, false] (cpmap [CpStep.Y]).cpring
          ++ listMask mc (ctrenum [CpStep.Y]) = [] := by
        rw [hM3, ctrenum_Y_nil, listMask_nil_list]
        rfl
      rwa [hcc] at hk
    · rw [hM3]
      rfl
  -- (false, false, true): the foot is contracted
  · change CfctrSpec [CpStep.Y] [false, false, true] mc []
    intro k hk
    have hcc : listMask [false, false, true] (cpmap [CpStep.Y]).cpring
        ++ listMask mc (ctrenum [CpStep.Y])
        = ([(cpmap ([] : CProg)).point]).map (injcpStep CpStep.Y []) := by
      rw [hM3, ctrenum_Y_nil, listMask_nil_list]
      rfl
    have hX : k (cpmap [CpStep.Y]).point
        = k ((cpmap [CpStep.Y]).map.edge
            ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point)) :=
      congr_of_sameCycle hk.face (cface_edge_node_ecpY (cpmap []))
    have hne : k ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point)
        ≠ k (cpmap [CpStep.Y]).point := by
      intro hcontra
      have hmem := (hk.edge ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point)).mp
        (by rw [← hX, ← hcontra])
      rw [hcc, insertE_map (cpmap ([] : CProg)).map (cpmap [CpStep.Y]).map
        (injcpStep CpStep.Y []) (fun _ => rfl) _] at hmem
      refine notMem_map_injcpY_new [] _ ?_ hmem
      rw [show (cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point
        = (EcpDart.icp EcpDart.Xe : (cpmap [CpStep.Y]).Dart) from PointedMap.node_ecpY (cpmap [])]
      exact List.Mem.head _
    refine ⟨fun b => cond b (k (cpmap [CpStep.Y]).point)
      (k ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point)), ⟨?_, ?_⟩, ?_⟩
    · intro b
      cases b
      · exact fun hcon => hne hcon.symm
      · exact hne
    · intro b
      rw [hface0]
    · rw [hG0ring, hM3]
      rfl
  -- (false, true, false): the second outer ring edge is contracted
  · change CfctrSpec [CpStep.Y] [false, true, false] mc []
    intro k hk
    have hcc : listMask [false, true, false] (cpmap [CpStep.Y]).cpring
        ++ listMask mc (ctrenum [CpStep.Y])
        = listMask [false, true]
            [(cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point,
              (cpmap [CpStep.Y]).point] := by
      rw [hM3, ctrenum_Y_nil, listMask_nil_list]
      rfl
    have hnG : k ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point)
        = k (injcpStep CpStep.Y [] ((cpmap ([] : CProg)).map.node (cpmap ([] : CProg)).point)) :=
      congr_of_sameCycle hk.face (PointedMap.cface_node_ecpY' (cpmap []))
    refine ⟨fun b => k (injcpStep CpStep.Y [] b), ⟨?_, ?_⟩, ?_⟩
    · intro b
      rw [congrArg k (edge_injcpStep (s := CpStep.Y) trivial [] b)]
      intro hcon
      have hmem := (hk.edge (injcpStep CpStep.Y [] b)).mp hcon
      rw [hcc] at hmem
      exact notMem_insertE_new_Y [] [false, true] b hmem
    · intro b
      rw [hface0]
    · have hmapeq : ((cpmap ([] : CProg)).cpring).map (fun b => k (injcpStep CpStep.Y [] b))
          = [k ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point),
             k (injcpStep CpStep.Y [] (cpmap ([] : CProg)).point)] := by
        rw [hG0ring, hnG]
        rfl
      rw [hmapeq, hM3]
      rfl
  -- (true, false, false): the first outer ring edge is contracted
  · change CfctrSpec [CpStep.Y] [true, false, false] mc []
    intro k hk
    have hcc : listMask [true, false, false] (cpmap [CpStep.Y]).cpring
        ++ listMask mc (ctrenum [CpStep.Y])
        = listMask [true, false]
            [(cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point,
              (cpmap [CpStep.Y]).point] := by
      rw [hM3, ctrenum_Y_nil, listMask_nil_list]
      rfl
    have hnG : k ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point)
        = k (injcpStep CpStep.Y [] ((cpmap ([] : CProg)).map.node (cpmap ([] : CProg)).point)) :=
      congr_of_sameCycle hk.face (PointedMap.cface_node_ecpY' (cpmap []))
    have hX : k (cpmap [CpStep.Y]).point
        = k ((cpmap [CpStep.Y]).map.edge
            ((cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point)) :=
      congr_of_sameCycle hk.face (cface_edge_node_ecpY (cpmap []))
    have hmem : (cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point
        ∈ (cpmap [CpStep.Y]).map.insertE
          (listMask [true, false, false] (cpmap [CpStep.Y]).cpring
            ++ listMask mc (ctrenum [CpStep.Y])) := by
      rw [hcc]
      exact mem_insertE_self _ (List.Mem.head _)
    have hE := (hk.edge _).mpr hmem
    refine ⟨fun b => k (injcpStep CpStep.Y [] b), ⟨?_, ?_⟩, ?_⟩
    · intro b
      rw [congrArg k (edge_injcpStep (s := CpStep.Y) trivial [] b)]
      intro hcon
      have hmem2 := (hk.edge (injcpStep CpStep.Y [] b)).mp hcon
      rw [hcc] at hmem2
      exact notMem_insertE_new_Y [] [true, false] b hmem2
    · intro b
      rw [hface0]
    · have hkey : k (injcpStep CpStep.Y []
            ((cpmap ([] : CProg)).map.node (cpmap ([] : CProg)).point))
          = k (cpmap [CpStep.Y]).point := hnG.symm.trans (hE.symm.trans hX.symm)
      have hmapeq : ((cpmap ([] : CProg)).cpring).map (fun b => k (injcpStep CpStep.Y [] b))
          = [k (cpmap [CpStep.Y]).point,
             k (injcpStep CpStep.Y [] (cpmap ([] : CProg)).point)] := by
        rw [hG0ring, ← hkey]
        rfl
      rw [hmapeq, hM3]
      rfl

/-- **The `H` step of `cfctr_correct`, contracted crossbar**: when the contract
erases the crossbar of the `H`, sparseness forces it to erase nothing else at
this junction, and the step disappears. -/
private theorem cfctrSpec_H_crossbar {cp : CProg} (hp : (cpmap cp).Proper)
    (mr' mc' : List Bool) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (false :: false :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (false :: false :: mr') (true :: false :: false :: mc') cpc₀ := by
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp false false true false false mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  refine ⟨h', hcol', ?_⟩
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hEh : (listMask ((false :: false :: mr').map not) (cpmap cp).cpring).map h
      = h ((cpmap cp).map.node (cpmap cp).point) :: h (cpmap cp).point
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGprop]
    rfl
  have hT : (listMask ((false :: false :: mr').map not) (cpmap (.H :: cp)).cpring).map k
      = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
        :: k (cpmap (.H :: cp)).point
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    rw [hMring, show ((false :: false :: mr').map not) = true :: true :: mr'.map not from rfl,
      listMask_true, listMask_true, listMask_map, List.map_cons, List.map_cons, List.map_map]
    congr 2
    exact List.map_congr_left (fun x _ => (hh x).symm)
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hmemfX : (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point
      ∈ (cpmap (.H :: cp)).map.insertE
        (listMask (false :: false :: mr') (cpmap (.H :: cp)).cpring
          ++ listMask (true :: false :: false :: mc') (ctrenum (.H :: cp))) := by
    refine mem_insertE_self _ (List.mem_append_right _ ?_)
    rw [ctrenum_H]
    exact List.Mem.head _
  have hefX := (hk.edge _).mpr hmemfX
  have hfX : k (cpmap (.H :: cp)).point
      = k ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point) :=
    congr_of_sameCycle hk.face ((cpmap (.H :: cp)).map.cface_face _)
  have hpt : k ((cpmap (.H :: cp)).map.edge
      ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point))
      = k (injcpStep CpStep.H cp (cpmap cp).point) :=
    congr_of_sameCycle hk.face (cface_edge_face_ecpH (cpmap cp) hp)
  rw [Eh, hEh, hT, hh, hh, ← hnG, ← hpt, hefX, ← hfX]

/-- After an `H` step the new dart lies on the face of the edge of its node. -/
private theorem cface_edge_node_ecpH (M : PointedMap) (hp : M.Proper) :
    M.ecpH.map.CFace M.ecpH.point (M.ecpH.map.edge (M.ecpH.map.node M.ecpH.point)) := by
  rw [show M.ecpH.map.node M.ecpH.point = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : M.ecpH.Dart)
    from PointedMap.node_ecpH M hp]
  exact (PointedMap.cface_ecpH M hp _).mpr (Or.inr (Or.inr rfl))

/-- The reference dart lies on the face of the edge of its node. -/
private theorem cface_edge_node_self {D : Type*} [Finite D] (G : Hypermap D) (x₀ : D) :
    G.CFace x₀ (G.edge (G.node x₀)) := by
  have h1 : G.face (G.edge (G.node x₀)) = x₀ := by
    rw [Hypermap.face_edge, Hypermap.inv_node_node]
  have h2 : G.CFace (G.edge (G.node x₀)) (G.face (G.edge (G.node x₀))) := G.cface_face _
  rw [h1] at h2
  exact h2.symm

/-- **The `H` step of `cfctr_correct`, contracted left foot and right ring
edge**: the step disappears. -/
private theorem cfctrSpec_H_erase1 {cp : CProg} (hp : (cpmap cp).Proper)
    (mr' mc' : List Bool) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (false :: true :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (true :: false :: mr') (false :: false :: true :: mc') cpc₀ := by
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp true false false false true mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  refine ⟨h', hcol', ?_⟩
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hEh : (listMask ((false :: true :: mr').map not) (cpmap cp).cpring).map h
      = h ((cpmap cp).map.node (cpmap cp).point)
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGprop]
    rfl
  have hT : (listMask ((true :: false :: mr').map not) (cpmap (.H :: cp)).cpring).map k
      = k (cpmap (.H :: cp)).point
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    rw [hMring, show ((true :: false :: mr').map not) = false :: true :: mr'.map not from rfl,
      listMask_false, listMask_true, listMask_map, List.map_cons, List.map_map]
    congr 1
    exact List.map_congr_left (fun x _ => (hh x).symm)
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hmem : (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
      ∈ (cpmap (.H :: cp)).map.insertE
        (listMask (true :: false :: mr') (cpmap (.H :: cp)).cpring
          ++ listMask (false :: false :: true :: mc') (ctrenum (.H :: cp))) := by
    refine mem_insertE_self _ (List.mem_append_left _ ?_)
    rw [hMring]
    exact List.Mem.head _
  have hE := (hk.edge _).mpr hmem
  have hX : k (cpmap (.H :: cp)).point
      = k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpH (cpmap cp) hp)
  rw [Eh, hEh, hT, hh, ← hnG, ← hE, ← hX]

/-- **The `H` step of `cfctr_correct`, contracted right foot and left ring
edge**: the step disappears. -/
private theorem cfctrSpec_H_erase2 {cp : CProg} (hp : (cpmap cp).Proper)
    (mr' mc' : List Bool) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (true :: false :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (false :: true :: mr') (false :: true :: false :: mc') cpc₀ := by
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp false true false true false mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  refine ⟨h', hcol', ?_⟩
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hEh : (listMask ((true :: false :: mr').map not) (cpmap cp).cpring).map h
      = h (cpmap cp).point :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGprop]
    rfl
  have hT : (listMask ((false :: true :: mr').map not) (cpmap (.H :: cp)).cpring).map k
      = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    rw [hMring, show ((false :: true :: mr').map not) = true :: false :: mr'.map not from rfl,
      listMask_true, listMask_false, listMask_map, List.map_cons, List.map_map]
    congr 1
    exact List.map_congr_left (fun x _ => (hh x).symm)
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hmemG : (cpmap cp).map.node (cpmap cp).point
      ∈ (cpmap cp).map.insertE
        (listMask (true :: false :: mr') (cpmap cp).cpring ++ listMask mc' (ctrenum cp)) := by
    refine mem_insertE_self _ (List.mem_append_left _ ?_)
    rw [hGprop]
    exact List.Mem.head _
  have hEg := (hcc.edge _).mpr hmemG
  have hptG : h (cpmap cp).point = h ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hcc.face (cface_edge_node_self (cpmap cp).map (cpmap cp).point)
  rw [Eh, hEh, hT, hptG, hEg, hh, ← hnG]

/-- **The `H` step of `cfctr_correct`, both feet contracted**: the kernel face
the step closes is cut off from the ring, and the step becomes a `U` step. -/
private theorem cfctrSpec_H_U {cp : CProg} (hp : (cpmap cp).Proper)
    (mr' mc' : List Bool) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (true :: true :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (false :: false :: mr') (false :: true :: true :: mc')
      (.U :: cpc₀) := by
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp false false false true true mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hEh : (listMask ((true :: true :: mr').map not) (cpmap cp).cpring).map h
      = (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGprop]
    rfl
  rw [hEh] at Eh
  -- walk along the erased stretch of the ring
  have hEr : ∀ y ∈ listMask (true :: true :: mr') (cpmap cp).cpring,
      h ((cpmap cp).map.edge y) = h y := fun y hy =>
    (hcc.edge y).mpr (mem_insertE_self _ (List.mem_append_left _ hy))
  have hchain : List.IsChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).map.node (cpmap cp).point
        :: (cpmap cp).point :: (cpmap cp).cpring.drop 2) := by
    have h0 : List.IsChain (fun u v => u = (cpmap cp).map.node v) (cpmap cp).cpring :=
      (Hypermap.isCyclicChain_cpring (G := (cpmap cp).map) (x₀ := (cpmap cp).point)).isChain
    rw [hGprop] at h0
    exact h0
  obtain ⟨z, l', hzl⟩ : ∃ z l', listMask (mr'.map not) ((cpmap cp).cpring.drop 2) = z :: l' := by
    match hm : listMask (mr'.map not) ((cpmap cp).cpring.drop 2) with
    | z :: l' => exact ⟨z, l', rfl⟩
    | [] =>
      exfalso
      rw [hm, List.map_nil] at Eh
      refine Hypermap.cpring_ne_nil (G := (cpmap cpc₀).map) (x₀ := (cpmap cpc₀).point) ?_
      rcases hcpr : (cpmap cpc₀).cpring with _ | ⟨a, t⟩
      · exact hcpr
      · rw [hcpr] at Eh; simp at Eh
  have hwalk : h z = h ((cpmap cp).map.node (cpmap cp).point) := by
    refine head_listMask_not hcc.face (true :: true :: mr') _ _ hchain
      (fun y hy => hEr y (by rw [hGprop]; exact hy)) z l' hzl
  have hGcring : (cpmap cpc₀).cpring
      = (cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).cpring.tail :=
    Hypermap.head_cpring
  have h'nGc : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
      = h ((cpmap cp).map.node (cpmap cp).point) := by
    have h2 := Eh
    rw [hGcring, hzl] at h2
    rw [List.map_cons, List.map_cons] at h2
    injection h2 with h3 _
    rw [h3, hwalk]
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hX : k (cpmap (.H :: cp)).point
      = k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpH (cpmap cp) hp)
  have hccM : listMask (false :: false :: mr') (cpmap (.H :: cp)).cpring
        ++ listMask (false :: true :: true :: mc') (ctrenum (.H :: cp))
      = (listMask mr' ((cpmap cp).cpring.drop 2)
          ++ listMask (true :: true :: mc')
              ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
                :: ctrenum cp)).map (injcpStep CpStep.H cp) := by
    rw [hMring, ctrenum_H, listMask_false, listMask_false, listMask_false, listMask_map,
      listMask_map, List.map_append]
  have hnXX : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      ≠ k (cpmap (.H :: cp)).point := by
    intro hcontra
    have h1 : k ((cpmap (.H :: cp)).map.edge
        ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point))
        = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point) := by
      rw [← hX, ← hcontra]
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpH_new cp _ ?_ h2
    rw [show (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
      = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : (cpmap (.H :: cp)).Dart) from
      PointedMap.node_ecpH (cpmap cp) hp]
    exact List.Mem.head _
  -- the colouring of the `U` step
  have hface : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.U :: cpc₀)).map.CFace (injcpStep .U cpc₀ x) (injcpStep .U cpc₀ y)
        ↔ (cpmap cpc₀).map.CFace x y :=
    fun x y => Hypermap.cface_icpU (cpmap cpc₀).map (cpmap cpc₀).point x y
  have hcc' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.U :: cpc₀)).map.CFace (injcpStep .U cpc₀ x) (injcpStep .U cpc₀ y)
        → h' x = h' y := fun x y hxy => hcol'.cface ((hface x y).mp hxy)
  have hk'X : extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.H :: cp)).point) (cpmap (.U :: cpc₀)).point
      = k (cpmap (.H :: cp)).point := by
    refine extColoring_eq_of_not ?_
    rintro ⟨x, hx⟩
    have hxx : (EcpDart.icp x : EcpDart (cpmap cpc₀).Dart) = EcpDart.X :=
      (Hypermap.cface_ecpU (cpmap cpc₀).map (cpmap cpc₀).point _).mp hx
    exact absurd hxx (by simp)
  have hk'Xe : extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.H :: cp)).point)
        ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
      = h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) := by
    have hface1 : (cpmap (.U :: cpc₀)).map.CFace
        ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
        (injcpStep .U cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point)) :=
      (Hypermap.cface_Xe_icpU (cpmap cpc₀).map (cpmap cpc₀).point
        ((cpmap cpc₀).map.node (cpmap cpc₀).point)).mpr (Equiv.Perm.SameCycle.refl _ _)
    rw [extColoring_congr hcc' hface1]
    exact extColoring_apply hface hcol'.face _
  have hk'ne : extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.H :: cp)).point)
        ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
      ≠ extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
        (k (cpmap (.H :: cp)).point) (cpmap (.U :: cpc₀)).point := by
    rw [hk'Xe, hk'X, h'nGc, hh, ← hnG]
    exact hnXX
  refine ⟨extColoring (cpmap (.U :: cpc₀)).map (injcpStep .U cpc₀) h'
    (k (cpmap (.H :: cp)).point), ?_, ?_⟩
  · refine coloring_extColoring hface
      (fun x y hxy => (Hypermap.adj_icpU (cpmap cpc₀).map (cpmap cpc₀).point x y).mp hxy)
      hcol' (fun u => Hypermap.fband_icpU (cpmap cpc₀).map (cpmap cpc₀).point u) ?_ ?_
    · intro u hu
      obtain rfl : u = (cpmap (.U :: cpc₀)).point :=
        (Hypermap.cface_ecpU (cpmap cpc₀).map (cpmap cpc₀).point u).mp hu
      exact hk'ne
    · intro u hu
      have hu2 : (cpmap (.U :: cpc₀)).map.edge u = (cpmap (.U :: cpc₀)).point :=
        (Hypermap.cface_ecpU (cpmap cpc₀).map (cpmap cpc₀).point _).mp hu
      have hu3 : u = (cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point := by
        have h4 : (cpmap (.U :: cpc₀)).map.edge
            ((cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point)
            = (cpmap (.U :: cpc₀)).point := rfl
        exact (cpmap (.U :: cpc₀)).map.edge.injective (hu2.trans h4.symm)
      rw [hu3] at hu2
      rw [hu3, hu2, hk'X, hk'Xe, h'nGc, hh, ← hnG]
      exact fun hcon => hnXX hcon.symm
  · have hNring : (cpmap (.U :: cpc₀)).cpring
        = (cpmap (.U :: cpc₀)).map.edge (cpmap (.U :: cpc₀)).point
          :: (cpmap (.U :: cpc₀)).point
          :: (cpmap cpc₀).cpring.map (injcpStep .U cpc₀) :=
      PointedMap.cpring_ecpU' (cpmap cpc₀)
    have hT : (listMask ((false :: false :: mr').map not) (cpmap (.H :: cp)).cpring).map k
        = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
          :: k (cpmap (.H :: cp)).point
          :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
      rw [hMring, show ((false :: false :: mr').map not) = true :: true :: mr'.map not from rfl,
        listMask_true, listMask_true, listMask_map, List.map_cons, List.map_cons, List.map_map]
      congr 2
      exact List.map_congr_left (fun x _ => (hh x).symm)
    rw [hNring, hT, List.map_cons, List.map_cons, List.map_map, hk'Xe, hk'X, h'nGc, hh, ← hnG]
    congr 2
    rw [← Eh]
    exact List.map_congr_left (fun x _ => extColoring_apply hface hcol'.face x)

/-- **The `H` step of `cfctr_correct`, one foot contracted**: the step loses one
of its two feet and becomes a `Y` step. -/
private theorem cfctrSpec_H_Y {cp : CProg} (hlong : (cpmap cp).Long) {b₄ b₅ : Bool}
    (hb : (b₄ = true ∧ b₅ = false) ∨ (b₄ = false ∧ b₅ = true))
    (mr' mc' : List Bool) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (b₄ :: b₅ :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (false :: false :: mr') (false :: b₄ :: b₅ :: mc')
      (.Y :: cpc₀) := by
  have hp : (cpmap cp).Proper := hlong.proper
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp false false false b₄ b₅ mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  have hGlong : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
      :: (cpmap cp).cpring.drop 3 := Hypermap.head_long_cpring hlong
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hdrop2 : (cpmap cp).cpring.drop 2
      = (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
        :: (cpmap cp).cpring.drop 3 := by
    conv_lhs => rw [hGlong]
    rfl
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hMlong : (cpmap (.H :: cp)).Long := by
    refine (PointedMap.long_iff _).mpr ?_
    have h1 : (cpmap (.H :: cp)).cpring.length = (cpmap cp).cpring.length :=
      PointedMap.length_cpring_ecpH_all (cpmap cp)
    rw [h1]
    exact (PointedMap.long_iff _).mp hlong
  have hMlongring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: (cpmap (.H :: cp)).map.face
            ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
        :: (cpmap (.H :: cp)).cpring.drop 3 := Hypermap.head_long_cpring hMlong
  have hfeM : (cpmap (.H :: cp)).map.face
        ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
      = injcpStep .H cp ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) := by
    have h1 : (cpmap (.H :: cp)).cpring
        = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
          :: injcpStep .H cp ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))
          :: ((cpmap cp).cpring.drop 3).map (injcpStep CpStep.H cp) := by
      rw [hMring, hdrop2, List.map_cons]
    have h2 := hMlongring.symm.trans h1
    have h3 := congrArg (fun l => l.tail.tail.head?) h2
    simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h3
    exact h3
  -- the recursive ring equation, split at its head
  obtain ⟨z, hz⟩ : ∃ z, listMask ((b₄ :: b₅ :: mr').map not)
      ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: (cpmap cp).cpring.drop 2)
      = z :: listMask (mr'.map not) ((cpmap cp).cpring.drop 2) := by
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(cpmap cp).point, rfl⟩
    · exact ⟨(cpmap cp).map.node (cpmap cp).point, rfl⟩
  have hEh : (listMask ((b₄ :: b₅ :: mr').map not) (cpmap cp).cpring).map h
      = h z :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGprop]
    rw [hz, List.map_cons]
  rw [hEh] at Eh
  -- walking along the erased stretch of the ring
  have hEr : ∀ y ∈ listMask (b₄ :: b₅ :: mr') (cpmap cp).cpring,
      h ((cpmap cp).map.edge y) = h y := fun y hy =>
    (hcc.edge y).mpr (mem_insertE_self _ (List.mem_append_left _ hy))
  have hchain : List.IsChain (fun u v => u = (cpmap cp).map.node v) (cpmap cp).cpring :=
    (Hypermap.isCyclicChain_cpring (G := (cpmap cp).map) (x₀ := (cpmap cp).point)).isChain
  have hchain2 : List.IsChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).map.node (cpmap cp).point
        :: (cpmap cp).point :: (cpmap cp).cpring.drop 2) := by
    have h0 := hchain
    rw [hGprop] at h0
    exact h0
  have hwalk : h z = h ((cpmap cp).map.node (cpmap cp).point) := by
    refine head_listMask_not hcc.face (b₄ :: b₅ :: mr') _ _ hchain2
      (fun y hy => hEr y (by rw [hGprop]; exact hy)) z _ hz
  -- the second ring dart
  have hchain3 : List.IsChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
        :: (cpmap cp).cpring.drop 3) := by
    have h0 := hchain
    rw [hGlong] at h0
    exact ((List.isChain_cons_cons.mp h0).2 |> List.isChain_cons_cons.mp).2
  have hGcprop : (cpmap cpc₀).Proper := hcol'.properCpring (cpmap cpc₀).point
  have hGcring : (cpmap cpc₀).cpring
      = (cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).point
        :: (cpmap cpc₀).cpring.drop 2 := Hypermap.head_proper_cpring hGcprop
  obtain ⟨z₂, l₂, hz₂⟩ : ∃ z₂ l₂,
      listMask (mr'.map not) ((cpmap cp).cpring.drop 2) = z₂ :: l₂ := by
    match hm : listMask (mr'.map not) ((cpmap cp).cpring.drop 2) with
    | z₂ :: l₂ => exact ⟨z₂, l₂, rfl⟩
    | [] =>
      exfalso
      rw [hm, List.map_nil] at Eh
      rw [hGcring] at Eh
      simp at Eh
  have hsplit : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) = h z
      ∧ h' (cpmap cpc₀).point = h z₂
      ∧ ((cpmap cpc₀).cpring.drop 2).map h' = l₂.map h := by
    have h2 := Eh
    rw [hGcring, hz₂] at h2
    simp only [List.map_cons] at h2
    injection h2 with h3 h4
    injection h4 with h5 h6
    exact ⟨h3, h5, h6⟩
  have hsubmask : ∀ y ∈ listMask mr' ((cpmap cp).cpring.drop 2),
      y ∈ listMask (b₄ :: b₅ :: mr') (cpmap cp).cpring := by
    intro y hy
    rw [hGprop]
    cases b₄ <;> cases b₅ <;> simp only [listMask_true, listMask_false] <;>
      first
        | exact hy
        | exact List.Mem.tail _ hy
        | exact List.Mem.tail _ (List.Mem.tail _ hy)
  have hwalk2 : h z₂ = h ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) := by
    refine head_listMask_not hcc.face mr' _ _ hchain3 (fun y hy => hEr y ?_) z₂ l₂ ?_
    · rw [← hdrop2] at hy
      exact hsubmask y hy
    · rw [← hdrop2]
      exact hz₂
  have h'nGc : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
      = h ((cpmap cp).map.node (cpmap cp).point) := hsplit.1.trans hwalk
  have h'Gc : h' (cpmap cpc₀).point
      = h ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) :=
    hsplit.2.1.trans hwalk2
  -- colours of the new face
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hX : k (cpmap (.H :: cp)).point
      = k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpH (cpmap cp) hp)
  have hccM : listMask (false :: false :: mr') (cpmap (.H :: cp)).cpring
        ++ listMask (false :: b₄ :: b₅ :: mc') (ctrenum (.H :: cp))
      = (listMask mr' ((cpmap cp).cpring.drop 2)
          ++ listMask (b₄ :: b₅ :: mc')
              ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
                :: ctrenum cp)).map (injcpStep CpStep.H cp) := by
    rw [hMring, ctrenum_H, listMask_false, listMask_false, listMask_false, listMask_map,
      listMask_map, List.map_append]
  have hnXX : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      ≠ k (cpmap (.H :: cp)).point := by
    intro hcontra
    have h1 : k ((cpmap (.H :: cp)).map.edge
        ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point))
        = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point) := by
      rw [← hX, ← hcontra]
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpH_new cp _ ?_ h2
    rw [show (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
      = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : (cpmap (.H :: cp)).Dart) from
      PointedMap.node_ecpH (cpmap cp) hp]
    exact List.Mem.head _
  have hXne : k (injcpStep .H cp ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)))
      ≠ k (cpmap (.H :: cp)).point := by
    have hEq : k ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
        = k (injcpStep .H cp
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))) := by
      rw [← hfeM]
      exact congr_of_sameCycle hk.face
        ((cpmap (.H :: cp)).map.cface_face
          ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point))
    intro hcontra
    have h1 : k ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
        = k (cpmap (.H :: cp)).point := hEq.trans hcontra
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpH_new cp _ ?_ h2
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  -- the colouring of the `Y` step above
  have hface' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (injcpStep .Y cpc₀ x) (injcpStep .Y cpc₀ y)
        ↔ (cpmap cpc₀).map.CFace x y := cface_injcpY cpc₀
  have hcc' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (injcpStep .Y cpc₀ x) (injcpStep .Y cpc₀ y)
        → h' x = h' y := fun x y hxy => hcol'.cface ((hface' x y).mp hxy)
  have hfaceX : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (cpmap (.Y :: cpc₀)).point u
        ↔ u = (cpmap (.Y :: cpc₀)).point
          ∨ u = (cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point :=
    fun u => PointedMap.cface_ecpY (cpmap cpc₀) u
  have hadjY : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.Adj (cpmap (.Y :: cpc₀)).point u
        ↔ (cpmap (.Y :: cpc₀)).map.CFace u
              (injcpStep .Y cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point))
          ∨ (cpmap (.Y :: cpc₀)).map.CFace u (injcpStep .Y cpc₀ (cpmap cpc₀).point) :=
    fun u => PointedMap.adj_ecpY (cpmap cpc₀) hGcprop u
  have hk'X : extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
        (k (cpmap (.H :: cp)).point) (cpmap (.Y :: cpc₀)).point
      = k (cpmap (.H :: cp)).point :=
    extColoring_eq_of_not (fun hx => not_cface_injcpY cpc₀ hx.choose hx.choose_spec)
  have hcfnode : (cpmap (.Y :: cpc₀)).map.CFace
      ((cpmap (.Y :: cpc₀)).map.node (cpmap (.Y :: cpc₀)).point)
      (injcpStep .Y cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point)) :=
    PointedMap.cface_node_ecpY' (cpmap cpc₀)
  have hk'nX : extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
        (k (cpmap (.H :: cp)).point)
        ((cpmap (.Y :: cpc₀)).map.node (cpmap (.Y :: cpc₀)).point)
      = h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) := by
    rw [extColoring_congr hcc' hcfnode]
    exact extColoring_apply hface' hcol'.face _
  have hinv : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (cpmap (.Y :: cpc₀)).point
          ((cpmap (.Y :: cpc₀)).map.edge u)
        → (cpmap (.Y :: cpc₀)).map.edge ((cpmap (.Y :: cpc₀)).map.edge u) = u := by
    intro u hu
    rcases (hfaceX _).mp hu with he | he
    · have h1 : (cpmap (.Y :: cpc₀)).map.edge
          ((cpmap (.Y :: cpc₀)).map.edge (cpmap (.Y :: cpc₀)).point)
          = (cpmap (.Y :: cpc₀)).point := rfl
      have h2 : u = (cpmap (.Y :: cpc₀)).map.edge (cpmap (.Y :: cpc₀)).point :=
        (cpmap (.Y :: cpc₀)).map.edge.injective (he.trans h1.symm)
      rw [he, h2]
    · have h1 : (cpmap (.Y :: cpc₀)).map.edge
          ((cpmap (.Y :: cpc₀)).map.edge
            ((cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point))
          = (cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point := rfl
      have h2 : u = (cpmap (.Y :: cpc₀)).map.edge
          ((cpmap (.Y :: cpc₀)).map.face (cpmap (.Y :: cpc₀)).point) :=
        (cpmap (.Y :: cpc₀)).map.edge.injective (he.trans h1.symm)
      rw [he, h2]
  have hnew : ∀ u : (cpmap (.Y :: cpc₀)).Dart,
      (cpmap (.Y :: cpc₀)).map.CFace (cpmap (.Y :: cpc₀)).point u →
      extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
          (k (cpmap (.H :: cp)).point) ((cpmap (.Y :: cpc₀)).map.edge u)
        ≠ extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
          (k (cpmap (.H :: cp)).point) u := by
    intro u hu
    have hku : extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
        (k (cpmap (.H :: cp)).point) u = k (cpmap (.H :: cp)).point :=
      (extColoring_congr hcc' hu).symm.trans hk'X
    have hadjX : (cpmap (.Y :: cpc₀)).map.Adj (cpmap (.Y :: cpc₀)).point
        ((cpmap (.Y :: cpc₀)).map.edge u) :=
      ((cpmap (.Y :: cpc₀)).map.adj_congr_left hu _).mpr
        ((cpmap (.Y :: cpc₀)).map.adj_edge u)
    rw [hku]
    rcases (hadjY _).mp hadjX with hc | hc
    · rw [extColoring_congr hcc' hc, extColoring_apply hface' hcol'.face, h'nGc, hh, ← hnG]
      exact hnXX
    · rw [extColoring_congr hcc' hc, extColoring_apply hface' hcol'.face, h'Gc, hh]
      exact hXne
  refine ⟨extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
    (k (cpmap (.H :: cp)).point), ?_, ?_⟩
  · refine coloring_extColoring hface'
      (fun x y hxy => (PointedMap.adj_icpY' (cpmap cpc₀) x y).mp hxy) hcol'
      (fun u => fband_injcpY cpc₀ u) hnew ?_
    intro u hu
    have h1 := hnew _ hu
    rw [hinv u hu] at h1
    exact fun hcon => h1 hcon.symm
  · have hNring : (cpmap (.Y :: cpc₀)).cpring
        = (cpmap (.Y :: cpc₀)).map.node (cpmap (.Y :: cpc₀)).point
          :: (cpmap (.Y :: cpc₀)).point
          :: ((cpmap cpc₀).cpring.tail).map (injcpStep CpStep.Y cpc₀) :=
      PointedMap.cpring_ecpY' (cpmap cpc₀)
    have hT : (listMask ((false :: false :: mr').map not) (cpmap (.H :: cp)).cpring).map k
        = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
          :: k (cpmap (.H :: cp)).point
          :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
      rw [hMring, show ((false :: false :: mr').map not) = true :: true :: mr'.map not from rfl,
        listMask_true, listMask_true, listMask_map, List.map_cons, List.map_cons, List.map_map]
      congr 2
      exact List.map_congr_left (fun x _ => (hh x).symm)
    have hGctail : (cpmap cpc₀).cpring.tail
        = (cpmap cpc₀).point :: (cpmap cpc₀).cpring.drop 2 := by
      conv_lhs => rw [hGcring]
      rfl
    rw [hNring, hT]
    simp only [List.map_cons, List.map_map]
    rw [hk'nX, hk'X, h'nGc, hh, ← hnG, hGctail, hz₂]
    simp only [List.map_cons, Function.comp_apply]
    congr 2
    rw [show (extColoring (cpmap (.Y :: cpc₀)).map (injcpStep .Y cpc₀) h'
          (k (cpmap (.H :: cp)).point) ∘ injcpStep .Y cpc₀)
        = h' from funext (fun x => extColoring_apply hface' hcol'.face x),
      extColoring_apply hface' hcol'.face, hsplit.2.1, hsplit.2.2]

/-- **The `H` step of `cfctr_correct`, untouched step**: when the contract meets
neither the outer ring edges nor the crossbar nor the feet, the step survives. -/
private theorem cfctrSpec_H_H {cp : CProg} (hlong : (cpmap cp).Long)
    (mr' mc' : List Bool) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (false :: false :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (false :: false :: mr') (false :: false :: false :: mc')
      (.H :: cpc₀) := by
  have hp : (cpmap cp).Proper := hlong.proper
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp false false false false false mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  have hGlong : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
      :: (cpmap cp).cpring.drop 3 := Hypermap.head_long_cpring hlong
  have hGprop : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hdrop2 : (cpmap cp).cpring.drop 2
      = (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
        :: (cpmap cp).cpring.drop 3 := by
    conv_lhs => rw [hGlong]
    rfl
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hMlong : (cpmap (.H :: cp)).Long := by
    refine (PointedMap.long_iff _).mpr ?_
    have h1 : (cpmap (.H :: cp)).cpring.length = (cpmap cp).cpring.length :=
      PointedMap.length_cpring_ecpH_all (cpmap cp)
    rw [h1]
    exact (PointedMap.long_iff _).mp hlong
  have hMlongring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: (cpmap (.H :: cp)).map.face
            ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
        :: (cpmap (.H :: cp)).cpring.drop 3 := Hypermap.head_long_cpring hMlong
  have hfeM : (cpmap (.H :: cp)).map.face
        ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
      = injcpStep .H cp ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) := by
    have h1 : (cpmap (.H :: cp)).cpring
        = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
          :: injcpStep .H cp ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))
          :: ((cpmap cp).cpring.drop 3).map (injcpStep CpStep.H cp) := by
      rw [hMring, hdrop2, List.map_cons]
    have h2 := hMlongring.symm.trans h1
    have h3 := congrArg (fun l => l.tail.tail.head?) h2
    simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h3
    exact h3
  have hEh : (listMask ((false :: false :: mr').map not) (cpmap cp).cpring).map h
      = h ((cpmap cp).map.node (cpmap cp).point) :: h (cpmap cp).point
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGprop]
    rfl
  rw [hEh] at Eh
  have hEr : ∀ y ∈ listMask (false :: false :: mr') (cpmap cp).cpring,
      h ((cpmap cp).map.edge y) = h y := fun y hy =>
    (hcc.edge y).mpr (mem_insertE_self _ (List.mem_append_left _ hy))
  have hchain : List.IsChain (fun u v => u = (cpmap cp).map.node v) (cpmap cp).cpring :=
    (Hypermap.isCyclicChain_cpring (G := (cpmap cp).map) (x₀ := (cpmap cp).point)).isChain
  have hchain3 : List.IsChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
        :: (cpmap cp).cpring.drop 3) := by
    have h0 := hchain
    rw [hGlong] at h0
    exact ((List.isChain_cons_cons.mp h0).2 |> List.isChain_cons_cons.mp).2
  have hsubmask : ∀ y ∈ listMask mr' ((cpmap cp).cpring.drop 2),
      y ∈ listMask (false :: false :: mr') (cpmap cp).cpring := by
    intro y hy
    rw [hGprop]
    exact hy
  have hGcprop : (cpmap cpc₀).Proper := hcol'.properCpring (cpmap cpc₀).point
  have hGcring : (cpmap cpc₀).cpring
      = (cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).point
        :: (cpmap cpc₀).cpring.drop 2 := Hypermap.head_proper_cpring hGcprop
  have hsplit : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
        = h ((cpmap cp).map.node (cpmap cp).point)
      ∧ h' (cpmap cpc₀).point = h (cpmap cp).point
      ∧ ((cpmap cpc₀).cpring.drop 2).map h'
          = (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    have h2 := Eh
    rw [hGcring] at h2
    simp only [List.map_cons] at h2
    injection h2 with h3 h4
    injection h4 with h5 h6
    exact ⟨h3, h5, h6⟩
  -- colours of the new face
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hX : k (cpmap (.H :: cp)).point
      = k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpH (cpmap cp) hp)
  have hccM : listMask (false :: false :: mr') (cpmap (.H :: cp)).cpring
        ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))
      = (listMask mr' ((cpmap cp).cpring.drop 2)
          ++ listMask (false :: false :: mc')
              ((cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
                :: ctrenum cp)).map (injcpStep CpStep.H cp) := by
    rw [hMring, ctrenum_H, listMask_false, listMask_false, listMask_false, listMask_map,
      listMask_map, List.map_append]
  have hnXX : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      ≠ k (cpmap (.H :: cp)).point := by
    intro hcontra
    have h1 : k ((cpmap (.H :: cp)).map.edge
        ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point))
        = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point) := by
      rw [← hX, ← hcontra]
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpH_new cp _ ?_ h2
    rw [show (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
      = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : (cpmap (.H :: cp)).Dart) from
      PointedMap.node_ecpH (cpmap cp) hp]
    exact List.Mem.head _
  have hptne : k (injcpStep .H cp (cpmap cp).point) ≠ k (cpmap (.H :: cp)).point := by
    have hEq : k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point))
        = k (injcpStep .H cp (cpmap cp).point) :=
      congr_of_sameCycle hk.face (cface_edge_face_ecpH (cpmap cp) hp)
    have hfX : k (cpmap (.H :: cp)).point
        = k ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point) :=
      congr_of_sameCycle hk.face ((cpmap (.H :: cp)).map.cface_face _)
    intro hcontra
    have h1 : k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point))
        = k ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point) := by
      rw [hEq, hcontra, hfX]
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpH_new cp _ ?_ h2
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _))))
  have hwne : k (injcpStep .H cp ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)))
      ≠ k (cpmap (.H :: cp)).point := by
    have hEq : k ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
        = k (injcpStep .H cp
            ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point))) := by
      rw [← hfeM]
      exact congr_of_sameCycle hk.face
        ((cpmap (.H :: cp)).map.cface_face
          ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point))
    intro hcontra
    have h1 : k ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
        = k (cpmap (.H :: cp)).point := hEq.trans hcontra
    have h2 := (hk.edge _).mp h1
    rw [hccM, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map (injcpStep CpStep.H cp)
      (fun _ => rfl) _] at h2
    refine notMem_map_injcpH_new cp _ ?_ h2
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  -- the third ring dart of the contracted map
  have h'inv : h' ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point)
      ≠ k (cpmap (.H :: cp)).point := by
    by_cases hGclong : (cpmap cpc₀).Long
    · have hGclongring : (cpmap cpc₀).cpring
          = (cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).point
            :: (cpmap cpc₀).map.face ((cpmap cpc₀).map.edge (cpmap cpc₀).point)
            :: (cpmap cpc₀).cpring.drop 3 := Hypermap.head_long_cpring hGclong
      obtain ⟨z₂, l₂, hz₂⟩ : ∃ z₂ l₂,
          listMask (mr'.map not) ((cpmap cp).cpring.drop 2) = z₂ :: l₂ := by
        match hm : listMask (mr'.map not) ((cpmap cp).cpring.drop 2) with
        | z₂ :: l₂ => exact ⟨z₂, l₂, rfl⟩
        | [] =>
          exfalso
          have h2 := Eh
          rw [hGclongring, hm] at h2
          simp at h2
      have h4 : h' ((cpmap cpc₀).map.face ((cpmap cpc₀).map.edge (cpmap cpc₀).point))
          = h z₂ := by
        have h3 := Eh
        rw [hGclongring, hz₂] at h3
        have h5 := congrArg (fun l => l.tail.tail.head?) h3
        simp only [List.map_cons, List.tail_cons, List.head?_cons, Option.some.injEq] at h5
        exact h5
      have hwalk2 : h z₂
          = h ((cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)) := by
        refine head_listMask_not hcc.face mr' _ _ hchain3 (fun y hy => hEr y ?_) z₂ l₂ ?_
        · rw [← hdrop2] at hy
          exact hsubmask y hy
        · rw [← hdrop2]
          exact hz₂
      rw [show (cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point
        = (cpmap cpc₀).map.face ((cpmap cpc₀).map.edge (cpmap cpc₀).point) from
        (Hypermap.face_edge (cpmap cpc₀).map (cpmap cpc₀).point).symm ▸ rfl, h4, hwalk2, hh]
      exact hwne
    · have hinv : (cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point
          = (cpmap cpc₀).map.node (cpmap cpc₀).point := by
        by_contra hcon
        exact hGclong (Hypermap.longCpring_iff_inv_ne.mpr hcon)
      rw [hinv, hsplit.1, hh, ← hnG]
      exact hnXX
  -- the colouring of the `H` step above
  have hface' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.H :: cpc₀)).map.CFace (injcpStep .H cpc₀ x) (injcpStep .H cpc₀ y)
        ↔ (cpmap cpc₀).map.CFace x y := cface_injcpH cpc₀
  have hcc' : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.H :: cpc₀)).map.CFace (injcpStep .H cpc₀ x) (injcpStep .H cpc₀ y)
        → h' x = h' y := fun x y hxy => hcol'.cface ((hface' x y).mp hxy)
  have hnodeH : (cpmap (.H :: cpc₀)).map.node (cpmap (.H :: cpc₀)).point
      = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : (cpmap (.H :: cpc₀)).Dart) :=
    PointedMap.node_ecpH (cpmap cpc₀) hGcprop
  have hfaceX : ∀ u : (cpmap (.H :: cpc₀)).Dart,
      (cpmap (.H :: cpc₀)).map.CFace (cpmap (.H :: cpc₀)).point u
        ↔ u = (cpmap (.H :: cpc₀)).point
          ∨ u = (cpmap (.H :: cpc₀)).map.face (cpmap (.H :: cpc₀)).point
          ∨ u = (cpmap (.H :: cpc₀)).map.edge
              ((cpmap (.H :: cpc₀)).map.node (cpmap (.H :: cpc₀)).point) := by
    intro u
    rw [hnodeH]
    exact PointedMap.cface_ecpH (cpmap cpc₀) hGcprop u
  have hadjH : ∀ u : (cpmap (.H :: cpc₀)).Dart,
      (cpmap (.H :: cpc₀)).map.Adj (cpmap (.H :: cpc₀)).point u
        ↔ (cpmap (.H :: cpc₀)).map.CFace u
              (injcpStep .H cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point))
          ∨ (cpmap (.H :: cpc₀)).map.CFace u (injcpStep .H cpc₀ (cpmap cpc₀).point)
          ∨ (cpmap (.H :: cpc₀)).map.CFace u
              (injcpStep .H cpc₀ ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point)) :=
    fun u => PointedMap.adj_ecpH (cpmap cpc₀) hGcprop u
  have hk'X : extColoring (cpmap (.H :: cpc₀)).map (injcpStep .H cpc₀) h'
        (k (cpmap (.H :: cp)).point) (cpmap (.H :: cpc₀)).point
      = k (cpmap (.H :: cp)).point :=
    extColoring_eq_of_not (fun hx => not_cface_injcpH cpc₀ hGcprop hx.choose hx.choose_spec)
  have hcfnode : (cpmap (.H :: cpc₀)).map.CFace
      ((cpmap (.H :: cpc₀)).map.node (cpmap (.H :: cpc₀)).point)
      (injcpStep .H cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point)) :=
    PointedMap.cface_node_ecpH' (cpmap cpc₀) hGcprop
  have hk'nX : extColoring (cpmap (.H :: cpc₀)).map (injcpStep .H cpc₀) h'
        (k (cpmap (.H :: cp)).point)
        ((cpmap (.H :: cpc₀)).map.node (cpmap (.H :: cpc₀)).point)
      = h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) := by
    rw [extColoring_congr hcc' hcfnode]
    exact extColoring_apply hface' hcol'.face _
  have hinvH : ∀ u : (cpmap (.H :: cpc₀)).Dart,
      (cpmap (.H :: cpc₀)).map.CFace (cpmap (.H :: cpc₀)).point
          ((cpmap (.H :: cpc₀)).map.edge u)
        → (cpmap (.H :: cpc₀)).map.edge ((cpmap (.H :: cpc₀)).map.edge u) = u := by
    intro u hu
    rcases (hfaceX _).mp hu with he | he | he
    · have h1 : (cpmap (.H :: cpc₀)).map.edge
          ((cpmap (.H :: cpc₀)).map.edge (cpmap (.H :: cpc₀)).point)
          = (cpmap (.H :: cpc₀)).point := rfl
      have h2 : u = (cpmap (.H :: cpc₀)).map.edge (cpmap (.H :: cpc₀)).point :=
        (cpmap (.H :: cpc₀)).map.edge.injective (he.trans h1.symm)
      rw [he, h2]
    · have h1 : (cpmap (.H :: cpc₀)).map.edge
          ((cpmap (.H :: cpc₀)).map.edge
            ((cpmap (.H :: cpc₀)).map.face (cpmap (.H :: cpc₀)).point))
          = (cpmap (.H :: cpc₀)).map.face (cpmap (.H :: cpc₀)).point := rfl
      have h2 : u = (cpmap (.H :: cpc₀)).map.edge
          ((cpmap (.H :: cpc₀)).map.face (cpmap (.H :: cpc₀)).point) :=
        (cpmap (.H :: cpc₀)).map.edge.injective (he.trans h1.symm)
      rw [he, h2]
    · have h2 : u = (cpmap (.H :: cpc₀)).map.node (cpmap (.H :: cpc₀)).point :=
        (cpmap (.H :: cpc₀)).map.edge.injective he
      rw [he, h2, hnodeH]
      rfl
  have hnew : ∀ u : (cpmap (.H :: cpc₀)).Dart,
      (cpmap (.H :: cpc₀)).map.CFace (cpmap (.H :: cpc₀)).point u →
      extColoring (cpmap (.H :: cpc₀)).map (injcpStep .H cpc₀) h'
          (k (cpmap (.H :: cp)).point) ((cpmap (.H :: cpc₀)).map.edge u)
        ≠ extColoring (cpmap (.H :: cpc₀)).map (injcpStep .H cpc₀) h'
          (k (cpmap (.H :: cp)).point) u := by
    intro u hu
    have hku : extColoring (cpmap (.H :: cpc₀)).map (injcpStep .H cpc₀) h'
        (k (cpmap (.H :: cp)).point) u = k (cpmap (.H :: cp)).point :=
      (extColoring_congr hcc' hu).symm.trans hk'X
    have hadjX : (cpmap (.H :: cpc₀)).map.Adj (cpmap (.H :: cpc₀)).point
        ((cpmap (.H :: cpc₀)).map.edge u) :=
      ((cpmap (.H :: cpc₀)).map.adj_congr_left hu _).mpr
        ((cpmap (.H :: cpc₀)).map.adj_edge u)
    rw [hku]
    rcases (hadjH _).mp hadjX with hc | hc | hc
    · rw [extColoring_congr hcc' hc, extColoring_apply hface' hcol'.face, hsplit.1, hh, ← hnG]
      exact hnXX
    · rw [extColoring_congr hcc' hc, extColoring_apply hface' hcol'.face, hsplit.2.1, hh]
      exact hptne
    · rw [extColoring_congr hcc' hc, extColoring_apply hface' hcol'.face]
      exact h'inv
  refine ⟨extColoring (cpmap (.H :: cpc₀)).map (injcpStep .H cpc₀) h'
    (k (cpmap (.H :: cp)).point), ?_, ?_⟩
  · refine coloring_extColoring hface'
      (fun x y hxy => (PointedMap.adj_icpH' (cpmap cpc₀) x y).mp hxy) hcol'
      (fun u => fband_injcpH cpc₀ u) hnew ?_
    intro u hu
    have h1 := hnew _ hu
    rw [hinvH u hu] at h1
    exact fun hcon => h1 hcon.symm
  · have hNring : (cpmap (.H :: cpc₀)).cpring
        = (cpmap (.H :: cpc₀)).map.node (cpmap (.H :: cpc₀)).point
          :: (cpmap (.H :: cpc₀)).point
          :: ((cpmap cpc₀).cpring.drop 2).map (injcpStep CpStep.H cpc₀) :=
      PointedMap.cpring_ecpH' (cpmap cpc₀) hGcprop
    have hT : (listMask ((false :: false :: mr').map not) (cpmap (.H :: cp)).cpring).map k
        = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
          :: k (cpmap (.H :: cp)).point
          :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
      rw [hMring, show ((false :: false :: mr').map not) = true :: true :: mr'.map not from rfl,
        listMask_true, listMask_true, listMask_map, List.map_cons, List.map_cons, List.map_map]
      congr 2
      exact List.map_congr_left (fun x _ => (hh x).symm)
    rw [hNring, hT]
    simp only [List.map_cons, List.map_map]
    rw [hk'nX, hk'X, hsplit.1, hh, ← hnG]
    congr 2
    rw [show (extColoring (cpmap (.H :: cpc₀)).map (injcpStep .H cpc₀) h'
          (k (cpmap (.H :: cp)).point) ∘ injcpStep .H cpc₀)
        = h' from funext (fun x => extColoring_apply hface' hcol'.face x)]
    exact hsplit.2.2

/-! #### Walking around the ring to the dart before the reference dart

When the contract erases every ring edge after the reference dart, the colour of
the ring is constant along that stretch and the walk wraps around the ring: it
ends either at the first ring dart the mask leaves, or — if the mask leaves none
— at the dart that closes the ring cycle. -/

/-- The dart that follows `x` on the ring has the colour of the first dart the
mask leaves; when the mask leaves none the walk runs to the end of the chain and
lands on `c`. -/
private theorem walk_headD {D : Type*} [Finite D] {G : Hypermap D} {h : D → Color}
    (hF : ∀ x, h (G.face x) = h x) (c : D) :
    ∀ (m : List Bool) (x : D) (p : List D), m.length = p.length →
      List.IsChain (fun u v => u = G.node v) (x :: (p ++ [c])) →
      (∀ y ∈ listMask m p, h (G.edge y) = h y) →
      h (G.node⁻¹ x) = h ((listMask (m.map not) p).headD c) := by
  intro m
  induction m with
  | nil =>
    intro x p hlen hchain _
    cases p with
    | cons y p => simp at hlen
    | nil =>
      have hxc : x = G.node c := (List.isChain_cons_cons.mp hchain).1
      rw [hxc, Hypermap.inv_node_node]
      rfl
  | cons b m ih =>
    intro x p hlen hchain hedge
    cases p with
    | nil => simp at hlen
    | cons y p =>
      have hxy : x = G.node y := (List.isChain_cons_cons.mp hchain).1
      have hchain' : List.IsChain (fun u v => u = G.node v) (y :: (p ++ [c])) :=
        (List.isChain_cons_cons.mp hchain).2
      have hlen' : m.length = p.length := by simpa using hlen
      rw [hxy, Hypermap.inv_node_node]
      cases b with
      | false =>
        rw [show ((false :: m).map not) = true :: m.map not from rfl, listMask_true]
        rfl
      | true =>
        have hey : h (G.edge y) = h y :=
          hedge y (by rw [listMask_true]; exact List.Mem.head _)
        have h1 : h (G.node⁻¹ y) = h y := by
          rw [← Hypermap.face_edge, hF, hey]
        rw [show ((true :: m).map not) = false :: m.map not from rfl, listMask_false, ← h1]
        exact ih y p hlen' hchain'
          (fun w hw => hedge w (by rw [listMask_true]; exact List.Mem.tail _ hw))

/-- The tail of a cyclic chain, closed up by its head, is a chain. -/
private theorem isChain_tail_append_head {α : Type*} {e : α → α → Prop} {a : α} {l : List α}
    (h : IsCyclicChain e (a :: l)) : List.IsChain e (l ++ [a]) := by
  refine List.isChain_append.mpr ⟨?_, List.isChain_singleton a, ?_⟩
  · cases l with
    | nil => exact List.isChain_nil
    | cons b l => exact (List.isChain_cons_cons.mp h.isChain).2
  · intro x hx y hy
    have hy' : a = y := by simpa using hy
    rw [← hy']
    refine h.2 x ?_ a rfl
    cases l with
    | nil => simp at hx
    | cons b l => rwa [List.getLast?_cons_cons]

/-- **The ring of the contracted map, when both outer ring edges survive.**  The
head of the ring of the contracted map keeps the colour of the head of the ring
below, the rest of its ring lists the darts the mask leaves, and the dart before
its reference dart keeps the colour of the dart before the reference dart
below — the walk wrapping around the ring when the mask leaves nothing. -/
private theorem contracted_ring_head {cp cpc₀ : CProg} (hp : (cpmap cp).Proper)
    {mr' : List Bool} (hlen : mr'.length = ((cpmap cp).cpring.drop 2).length)
    {h : (cpmap cp).Dart → Color} {h' : (cpmap cpc₀).Dart → Color}
    (hF : ∀ x, h ((cpmap cp).map.face x) = h x)
    (hEr : ∀ y ∈ listMask mr' ((cpmap cp).cpring.drop 2),
      h ((cpmap cp).map.edge y) = h y)
    (hprop' : (cpmap cpc₀).Proper)
    (Eh : (cpmap cpc₀).cpring.map h'
      = h ((cpmap cp).map.node (cpmap cp).point) :: h (cpmap cp).point
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h) :
    h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
        = h ((cpmap cp).map.node (cpmap cp).point)
      ∧ ((cpmap cpc₀).cpring.drop 2).map h'
        = (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h
      ∧ h' ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point)
        = h ((cpmap cp).map.node⁻¹ (cpmap cp).point) := by
  have hGring : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hGcring : (cpmap cpc₀).cpring
      = (cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).point
        :: (cpmap cpc₀).cpring.drop 2 := Hypermap.head_proper_cpring hprop'
  have hsplit : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
        = h ((cpmap cp).map.node (cpmap cp).point)
      ∧ h' (cpmap cpc₀).point = h (cpmap cp).point
      ∧ ((cpmap cpc₀).cpring.drop 2).map h'
          = (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    have h2 := Eh
    rw [hGcring] at h2
    simp only [List.map_cons] at h2
    injection h2 with h3 h4
    injection h4 with h5 h6
    exact ⟨h3, h5, h6⟩
  have hnGc := hsplit.1
  have htail := hsplit.2.2
  -- the walk along the ring below
  have hcyc : IsCyclicChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).map.node (cpmap cp).point
        :: ((cpmap cp).point :: (cpmap cp).cpring.drop 2)) := by
    have h0 : IsCyclicChain (fun u v => u = (cpmap cp).map.node v) (cpmap cp).cpring :=
      Hypermap.isCyclicChain_cpring (G := (cpmap cp).map) (x₀ := (cpmap cp).point)
    rwa [hGring] at h0
  have hchainG : List.IsChain (fun u v => u = (cpmap cp).map.node v)
      ((cpmap cp).point :: ((cpmap cp).cpring.drop 2
        ++ [(cpmap cp).map.node (cpmap cp).point])) := isChain_tail_append_head hcyc
  have hwalk := walk_headD hF ((cpmap cp).map.node (cpmap cp).point) mr' (cpmap cp).point
    ((cpmap cp).cpring.drop 2) hlen hchainG hEr
  refine ⟨hnGc, htail, ?_⟩
  rcases hz : listMask (mr'.map not) ((cpmap cp).cpring.drop 2) with _ | ⟨z, l'⟩
  · -- the whole tail of the ring is erased: the contracted ring has two darts
    have hdrop : (cpmap cpc₀).cpring.drop 2 = [] := by
      have h1 := htail
      rw [hz, List.map_nil] at h1
      simpa using h1
    have hring2 : (cpmap cpc₀).cpring
        = [(cpmap cpc₀).map.node (cpmap cpc₀).point, (cpmap cpc₀).point] := by
      rw [hGcring, hdrop]
    have hcyc2 : IsCyclicChain (fun u v => u = (cpmap cpc₀).map.node v) (cpmap cpc₀).cpring :=
      Hypermap.isCyclicChain_cpring (G := (cpmap cpc₀).map) (x₀ := (cpmap cpc₀).point)
    have h2 := hcyc2.2 (cpmap cpc₀).point (by rw [hring2]; simp)
      ((cpmap cpc₀).map.node (cpmap cpc₀).point) (by rw [hring2]; simp)
    have hinv : (cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point
        = (cpmap cpc₀).map.node (cpmap cpc₀).point := by
      conv_lhs => rw [h2]
      rw [Hypermap.inv_node_node]
    have hw2 : h ((cpmap cp).map.node⁻¹ (cpmap cp).point)
        = h ((cpmap cp).map.node (cpmap cp).point) := by
      rw [hwalk, hz, List.headD_nil]
    rw [hinv, hnGc, hw2]
  · obtain ⟨w, l, hwl⟩ : ∃ w l, (cpmap cpc₀).cpring.drop 2 = w :: l := by
      rcases hd : (cpmap cpc₀).cpring.drop 2 with _ | ⟨w, l⟩
      · exfalso
        rw [hd, hz] at htail
        simp at htail
      · exact ⟨w, l, rfl⟩
    have hchainGc : List.IsChain (fun u v => u = (cpmap cpc₀).map.node v)
        ((cpmap cpc₀).map.node (cpmap cpc₀).point :: (cpmap cpc₀).point :: w :: l) := by
      have h0 : List.IsChain (fun u v => u = (cpmap cpc₀).map.node v) (cpmap cpc₀).cpring :=
        (Hypermap.isCyclicChain_cpring (G := (cpmap cpc₀).map)
          (x₀ := (cpmap cpc₀).point)).isChain
      rw [hGcring, hwl] at h0
      exact h0
    have hw : (cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point = w := by
      rw [(List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchainGc).2).1,
        Hypermap.inv_node_node]
    have hhw : h' w = h z ∧ l.map h' = l'.map h := by
      have h1 := htail
      rw [hwl, hz] at h1
      simp only [List.map_cons] at h1
      injection h1 with ha hb
      exact ⟨ha, hb⟩
    have hw2 : h ((cpmap cp).map.node⁻¹ (cpmap cp).point) = h z := by
      rw [hwalk, hz, List.headD_cons]
    rw [hw, hhw.1, hw2]

/-- A mask that is not all-`true` leaves at least one dart. -/
private theorem listMask_not_ne_nil {α : Type*} : ∀ (m : List Bool) (l : List α),
    m.length = l.length → ¬ m.all id = true → listMask (m.map not) l ≠ [] := by
  intro m
  induction m with
  | nil => intro l _ hall; exact absurd rfl hall
  | cons b m ih =>
    intro l hlen hall
    cases l with
    | nil => simp at hlen
    | cons x l =>
      have hlen' : m.length = l.length := by simpa using hlen
      cases b with
      | false =>
        rw [show ((false :: m).map not) = true :: m.map not from rfl, listMask_true]
        simp
      | true =>
        rw [show ((true :: m).map not) = false :: m.map not from rfl, listMask_false]
        exact ih l hlen' (fun hc => hall (by simp [hc]))

/-- The first new dart of a step is not an old one. -/
private theorem ecpDart_X_ne_icp {α : Type*} (v : α) :
    (EcpDart.X : EcpDart α) ≠ EcpDart.icp v := by simp

/-- The second new dart of a step is not an old one. -/
private theorem ecpDart_Xe_ne_icp {α : Type*} (v : α) :
    (EcpDart.Xe : EcpDart α) ≠ EcpDart.icp v := by simp

/-- The two new darts of a step are distinct. -/
private theorem ecpDart_Xe_ne_X {α : Type*} : (EcpDart.Xe : EcpDart α) ≠ EcpDart.X := by simp

/-- A new dart of an `H` step lies outside a contract made of one outer ring
dart and old darts. -/
private theorem notMem_insertE_consH (cp : CProg) (a : (cpmap (.H :: cp)).Dart)
    (L : List (cpmap cp).Dart) {u : (cpmap (.H :: cp)).Dart}
    (hu : u ∈ ([EcpDart.icp (EcpDart.icp EcpDart.Xe), EcpDart.icp (EcpDart.icp EcpDart.X),
      EcpDart.X, EcpDart.Xe, EcpDart.icp EcpDart.X, EcpDart.icp EcpDart.Xe] :
      List (cpmap (.H :: cp)).Dart))
    (h1 : u ≠ a) (h2 : u ≠ (cpmap (.H :: cp)).map.edge a) :
    u ∉ (cpmap (.H :: cp)).map.insertE (a :: L.map (injcpStep .H cp)) := by
  rw [Hypermap.insertE_cons, insertE_map (cpmap cp).map (cpmap (.H :: cp)).map
    (injcpStep CpStep.H cp) (fun _ => rfl) L]
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact h1 he
  rcases List.mem_cons.mp hm with he | hm
  · exact h2 he
  · exact notMem_map_injcpH_new cp _ hu hm

/-- **The `H` step of `cfctr_correct`, one outer ring edge and the opposite foot
contracted**: the junction loses one side entirely and becomes a `K` step, whose
new dart takes the colour of the outer ring dart the contract keeps. -/
private theorem cfctrSpec_H_K {cp : CProg} (hlong : (cpmap cp).Long) {b₁ b₂ : Bool}
    (hb : (b₁ = true ∧ b₂ = false) ∨ (b₁ = false ∧ b₂ = true))
    (mr' mc' : List Bool) (hlen : mr'.length = ((cpmap cp).cpring.drop 2).length)
    {cpc₀ : CProg} (hrec : CfctrSpec cp (false :: false :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (b₁ :: b₂ :: mr') (false :: false :: false :: mc')
      (.K :: cpc₀) := by
  have hp : (cpmap cp).Proper := hlong.proper
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp b₁ b₂ false false false mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  have hGring : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hEh : (listMask ((false :: false :: mr').map not) (cpmap cp).cpring).map h
      = h ((cpmap cp).map.node (cpmap cp).point) :: h (cpmap cp).point
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGring]
    rfl
  rw [hEh] at Eh
  have hEr : ∀ y ∈ listMask mr' ((cpmap cp).cpring.drop 2),
      h ((cpmap cp).map.edge y) = h y := fun y hy =>
    (hcc.edge y).mpr (mem_insertE_self _ (List.mem_append_left _ (by rw [hGring]; exact hy)))
  obtain ⟨hnGc, htail, hinvGc⟩ :=
    contracted_ring_head hp hlen hcc.face hEr (hcol'.properCpring (cpmap cpc₀).point) Eh
  -- the third ring dart of the `H` step
  have hdrop2 : (cpmap cp).cpring.drop 2
      = (cpmap cp).map.node⁻¹ (cpmap cp).point :: (cpmap cp).cpring.drop 3 := by
    have hlr : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
        :: (cpmap cp).map.node⁻¹ (cpmap cp).point :: (cpmap cp).cpring.drop 3 := by
      have h0 : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
          :: (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
          :: (cpmap cp).cpring.drop 3 := Hypermap.head_long_cpring hlong
      rwa [Hypermap.face_edge] at h0
    conv_lhs => rw [hlr]
    rfl
  have hMring3 : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: injcpStep .H cp ((cpmap cp).map.node⁻¹ (cpmap cp).point)
          :: ((cpmap cp).cpring.drop 3).map (injcpStep CpStep.H cp) := by
    rw [hMring, hdrop2, List.map_cons]
  have hinvM : (cpmap (.H :: cp)).map.node⁻¹ (cpmap (.H :: cp)).point
      = injcpStep .H cp ((cpmap cp).map.node⁻¹ (cpmap cp).point) := by
    have hchainM : List.IsChain (fun u v => u = (cpmap (.H :: cp)).map.node v)
        (cpmap (.H :: cp)).cpring :=
      (Hypermap.isCyclicChain_cpring (G := (cpmap (.H :: cp)).map)
        (x₀ := (cpmap (.H :: cp)).point)).isChain
    rw [hMring3] at hchainM
    rw [(List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchainM).2).1,
      Hypermap.inv_node_node]
  have hkeX : k ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
      = h ((cpmap cp).map.node⁻¹ (cpmap cp).point) := by
    rw [← hk.face ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point),
      Hypermap.face_edge, hinvM, hh]
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hKhead : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = h ((cpmap cp).map.node (cpmap cp).point) := by rw [hnG, hh]
  have hXnode : k (cpmap (.H :: cp)).point
      = k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpH (cpmap cp) hp)
  -- the contract of the step, split into its new and its old darts
  have hP : listMask (b₁ :: b₂ :: mr') (cpmap (.H :: cp)).cpring
      = listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
          (cpmap (.H :: cp)).point]
        ++ (listMask mr' ((cpmap cp).cpring.drop 2)).map (injcpStep CpStep.H cp) := by
    rw [hMring, ← listMask_map]
    exact listMask_append [b₁, b₂]
      [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point] rfl mr'
      (((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp))
  have hQ : listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))
      = (listMask mc' (ctrenum cp)).map (injcpStep CpStep.H cp) := by
    rw [ctrenum_H, List.map_cons, List.map_cons, listMask_false, listMask_false,
      listMask_false, listMask_map]
  have hccdec : listMask (b₁ :: b₂ :: mr') (cpmap (.H :: cp)).cpring
        ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))
      = listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
            (cpmap (.H :: cp)).point]
          ++ (listMask mr' ((cpmap cp).cpring.drop 2)
              ++ listMask mc' (ctrenum cp)).map (injcpStep CpStep.H cp) := by
    rw [hP, hQ, List.append_assoc, ← List.map_append]
  have hnodeX : (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
      = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : (cpmap (.H :: cp)).Dart) :=
    PointedMap.node_ecpH (cpmap cp) hp
  have hedgenX : (cpmap (.H :: cp)).map.edge
      ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = (EcpDart.icp (EcpDart.icp EcpDart.X) : (cpmap (.H :: cp)).Dart) := by
    rw [hnodeX]
    rfl
  have hpointX : (cpmap (.H :: cp)).point = (EcpDart.X : (cpmap (.H :: cp)).Dart) := rfl
  have hedgeX : (cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point
      = (EcpDart.Xe : (cpmap (.H :: cp)).Dart) := rfl
  have htl : (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map
        (k ∘ injcpStep CpStep.H cp)
      = (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h :=
    List.map_congr_left (fun x _ => (hh x).symm)
  -- the two shapes of the contract, and what they say about the new face
  have hcase : k ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
        ≠ k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      ∧ (listMask ((b₁ :: b₂ :: mr').map not) (cpmap (.H :: cp)).cpring).map k
        = h ((cpmap cp).map.node (cpmap cp).point)
          :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmem : (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
          ∈ (cpmap (.H :: cp)).map.insertE
            (listMask (true :: false :: mr') (cpmap (.H :: cp)).cpring
              ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))) :=
        mem_insertE_self _ (List.mem_append_left _ (by rw [hMring]; exact List.Mem.head _))
      have hE := (hk.edge _).mpr hmem
      have hXeq : k (cpmap (.H :: cp)).point
          = k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point) := hXnode.trans hE
      have hccA : listMask (true :: false :: mr') (cpmap (.H :: cp)).cpring
            ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))
          = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
            :: (listMask mr' ((cpmap cp).cpring.drop 2)
                ++ listMask mc' (ctrenum cp)).map (injcpStep CpStep.H cp) := hccdec
      have hXnot : (cpmap (.H :: cp)).point ∉ (cpmap (.H :: cp)).map.insertE
            (listMask (true :: false :: mr') (cpmap (.H :: cp)).cpring
              ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))) := by
        rw [hccA]
        refine notMem_insertE_consH cp _ _ ?_ ?_ ?_
        · rw [hpointX]
          exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
        · rw [hnodeX, hpointX]
          exact ecpDart_X_ne_icp _
        · rw [hedgenX, hpointX]
          exact ecpDart_X_ne_icp _
      refine ⟨fun hcon => hXnot ((hk.edge _).mp (hcon.trans hXeq.symm)), ?_⟩
      rw [hMring, show ((true :: false :: mr').map not) = false :: true :: mr'.map not from rfl,
        listMask_false, listMask_true, listMask_map, List.map_cons, List.map_map, htl, hXeq,
        hKhead]
    · have hmem : (cpmap (.H :: cp)).point
          ∈ (cpmap (.H :: cp)).map.insertE
            (listMask (false :: true :: mr') (cpmap (.H :: cp)).cpring
              ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))) :=
        mem_insertE_self _ (List.mem_append_left _ (by rw [hMring]; exact List.Mem.head _))
      have hEX := (hk.edge _).mpr hmem
      have hccB : listMask (false :: true :: mr') (cpmap (.H :: cp)).cpring
            ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))
          = (cpmap (.H :: cp)).point
            :: (listMask mr' ((cpmap cp).cpring.drop 2)
                ++ listMask mc' (ctrenum cp)).map (injcpStep CpStep.H cp) := hccdec
      have hnXnot : (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
          ∉ (cpmap (.H :: cp)).map.insertE
            (listMask (false :: true :: mr') (cpmap (.H :: cp)).cpring
              ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))) := by
        rw [hccB]
        refine notMem_insertE_consH cp _ _ ?_ ?_ ?_
        · rw [hnodeX]
          exact List.Mem.head _
        · rw [hnodeX, hpointX]
          exact (ecpDart_X_ne_icp _).symm
        · rw [hedgeX, hnodeX]
          exact (ecpDart_Xe_ne_icp _).symm
      refine ⟨?_, ?_⟩
      · intro hcon
        refine hnXnot ((hk.edge _).mp ?_)
        rw [← hXnode, ← hEX]
        exact hcon
      · rw [hMring,
          show ((false :: true :: mr').map not) = true :: false :: mr'.map not from rfl,
          listMask_true, listMask_false, listMask_map, List.map_cons, List.map_map, htl,
          hKhead]
  obtain ⟨hne, hT⟩ := hcase
  -- the colouring of the `K` step
  have hfaceK : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.K :: cpc₀)).map.CFace (injcpStep .K cpc₀ x) (injcpStep .K cpc₀ y)
        ↔ (cpmap cpc₀).map.CFace x y := PointedMap.cface_icpK (cpmap cpc₀)
  have hccK : ∀ x y : (cpmap cpc₀).Dart,
      (cpmap (.K :: cpc₀)).map.CFace (injcpStep .K cpc₀ x) (injcpStep .K cpc₀ y)
        → h' x = h' y := fun x y hxy => hcol'.cface ((hfaceK x y).mp hxy)
  have hk'old : ∀ x : (cpmap cpc₀).Dart,
      extColoring (cpmap (.K :: cpc₀)).map (injcpStep .K cpc₀) h'
        (k (cpmap (.H :: cp)).point) (injcpStep .K cpc₀ x) = h' x :=
    extColoring_apply hfaceK hcol'.face
  have hXeqK : (cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point
      = (EcpDart.X : (cpmap (.K :: cpc₀)).Dart) := PointedMap.node_point_ecpK (cpmap cpc₀)
  have hcfX : (cpmap (.K :: cpc₀)).map.CFace
      ((cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point)
      (injcpStep .K cpc₀ ((cpmap cpc₀).map.node (cpmap cpc₀).point)) := by
    rw [hXeqK]
    exact PointedMap.cface_node_ecpK (cpmap cpc₀)
  have hk'X : extColoring (cpmap (.K :: cpc₀)).map (injcpStep .K cpc₀) h'
        (k (cpmap (.H :: cp)).point)
        ((cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point)
      = h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) := by
    rw [extColoring_congr hccK hcfX]
    exact hk'old _
  have hcfXe : (cpmap (.K :: cpc₀)).map.CFace
      ((cpmap (.K :: cpc₀)).map.edge
        ((cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point))
      (injcpStep .K cpc₀ ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point)) := by
    have h1 : ((cpmap cpc₀).ecpK).map.CFace (EcpDart.Xe : ((cpmap cpc₀).ecpK).Dart)
        (EcpDart.icp ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point)) := by
      rw [PointedMap.map_ecpK (cpmap cpc₀)]
      exact (Hypermap.cface_Xe_icpN (cpmap cpc₀).map
          ((cpmap cpc₀).map.node (cpmap cpc₀).point)
          ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point)).mpr
        (by rw [Hypermap.inv_node_node])
    have h2 : (cpmap (.K :: cpc₀)).map.edge
        ((cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point)
        = (EcpDart.Xe : (cpmap (.K :: cpc₀)).Dart) := by rw [hXeqK]; rfl
    rw [h2]
    exact h1
  have hk'Xe : extColoring (cpmap (.K :: cpc₀)).map (injcpStep .K cpc₀) h'
        (k (cpmap (.H :: cp)).point)
        ((cpmap (.K :: cpc₀)).map.edge
          ((cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point))
      = h' ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point) := by
    rw [extColoring_congr hccK hcfXe]
    exact hk'old _
  have hk'ne : h' ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point)
      ≠ h' ((cpmap cpc₀).map.node (cpmap cpc₀).point) := by
    rw [hinvGc, hnGc, ← hkeX, ← hKhead]
    exact hne
  have hcolK : (cpmap (.K :: cpc₀)).map.Coloring
      (extColoring (cpmap (.K :: cpc₀)).map (injcpStep .K cpc₀) h'
        (k (cpmap (.H :: cp)).point)) := by
    refine ⟨?_, fun u => extColoring_congr hccK
      ((cpmap (.K :: cpc₀)).map.cface_face u).symm⟩
    intro u
    cases u with
    | X =>
      rw [← hXeqK, hk'Xe, hk'X]
      exact hk'ne
    | Xe =>
      have h1 : (cpmap (.K :: cpc₀)).map.edge (EcpDart.Xe : (cpmap (.K :: cpc₀)).Dart)
          = (cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point := by rw [hXeqK]; rfl
      have h2 : (EcpDart.Xe : (cpmap (.K :: cpc₀)).Dart)
          = (cpmap (.K :: cpc₀)).map.edge
              ((cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point) := by rw [hXeqK]; rfl
      rw [h1, h2, hk'X, hk'Xe]
      exact fun hcon => hk'ne hcon.symm
    | icp x =>
      have e1 : extColoring (cpmap (.K :: cpc₀)).map (injcpStep .K cpc₀) h'
            (k (cpmap (.H :: cp)).point)
            ((cpmap (.K :: cpc₀)).map.edge (EcpDart.icp x : (cpmap (.K :: cpc₀)).Dart))
          = h' ((cpmap cpc₀).map.edge x) := hk'old ((cpmap cpc₀).map.edge x)
      have e2 : extColoring (cpmap (.K :: cpc₀)).map (injcpStep .K cpc₀) h'
            (k (cpmap (.H :: cp)).point) (EcpDart.icp x : (cpmap (.K :: cpc₀)).Dart)
          = h' x := hk'old x
      rw [e1, e2]
      exact hcol'.edge x
  refine ⟨extColoring (cpmap (.K :: cpc₀)).map (injcpStep .K cpc₀) h'
    (k (cpmap (.H :: cp)).point), hcolK, ?_⟩
  have hKring : (cpmap (.K :: cpc₀)).cpring
      = (cpmap (.K :: cpc₀)).map.node (cpmap (.K :: cpc₀)).point
        :: ((cpmap cpc₀).cpring.drop 2).map (injcpStep .K cpc₀) := by
    rw [hXeqK]
    exact PointedMap.cpring_ecpK (cpmap cpc₀) (hcol'.properCpring (cpmap cpc₀).point)
  rw [hKring, hT, List.map_cons, List.map_map, hk'X, hnGc]
  congr 1
  rw [← htail]
  exact List.map_congr_left (fun x _ => hk'old x)

/-- **The `H` step of `cfctr_correct`, both outer ring edges contracted**: the
two ring faces the junction separates are merged, the step becomes an `A` step,
and the colouring is carried over unchanged. -/
private theorem cfctrSpec_H_A {cp : CProg} (hlong : (cpmap cp).Long)
    (mr' mc' : List Bool) (hlen : mr'.length = ((cpmap cp).cpring.drop 2).length)
    (hall : ¬ mr'.all id = true) {cpc₀ : CProg}
    (hrec : CfctrSpec cp (false :: false :: mr') mc' cpc₀) :
    CfctrSpec (.H :: cp) (true :: true :: mr') (false :: false :: false :: mc')
      (.A :: cpc₀) := by
  have hp : (cpmap cp).Proper := hlong.proper
  intro k hk
  obtain ⟨h, hh⟩ : ∃ h : (cpmap cp).Dart → Color, ∀ x, h x = k (injcpStep .H cp x) :=
    ⟨_, fun _ => rfl⟩
  have hcc := ccColoring_injcpH hp true true false false false mr' mc' hh hk
  obtain ⟨h', hcol', Eh⟩ := hrec h hcc
  have hGring : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hp
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: ((cpmap cp).cpring.drop 2).map (injcpStep CpStep.H cp) :=
    PointedMap.cpring_ecpH' (cpmap cp) hp
  have hEh : (listMask ((false :: false :: mr').map not) (cpmap cp).cpring).map h
      = h ((cpmap cp).map.node (cpmap cp).point) :: h (cpmap cp).point
        :: (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    conv_lhs => rw [hGring]
    rfl
  rw [hEh] at Eh
  have hEr : ∀ y ∈ listMask mr' ((cpmap cp).cpring.drop 2),
      h ((cpmap cp).map.edge y) = h y := fun y hy =>
    (hcc.edge y).mpr (mem_insertE_self _ (List.mem_append_left _ (by rw [hGring]; exact hy)))
  obtain ⟨hnGc, htail, hinvGc⟩ :=
    contracted_ring_head hp hlen hcc.face hEr (hcol'.properCpring (cpmap cpc₀).point) Eh
  have hdrop2 : (cpmap cp).cpring.drop 2
      = (cpmap cp).map.node⁻¹ (cpmap cp).point :: (cpmap cp).cpring.drop 3 := by
    have hlr : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
        :: (cpmap cp).map.node⁻¹ (cpmap cp).point :: (cpmap cp).cpring.drop 3 := by
      have h0 : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
          :: (cpmap cp).map.face ((cpmap cp).map.edge (cpmap cp).point)
          :: (cpmap cp).cpring.drop 3 := Hypermap.head_long_cpring hlong
      rwa [Hypermap.face_edge] at h0
    conv_lhs => rw [hlr]
    rfl
  have hMring3 : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: injcpStep .H cp ((cpmap cp).map.node⁻¹ (cpmap cp).point)
          :: ((cpmap cp).cpring.drop 3).map (injcpStep CpStep.H cp) := by
    rw [hMring, hdrop2, List.map_cons]
  have hinvM : (cpmap (.H :: cp)).map.node⁻¹ (cpmap (.H :: cp)).point
      = injcpStep .H cp ((cpmap cp).map.node⁻¹ (cpmap cp).point) := by
    have hchainM : List.IsChain (fun u v => u = (cpmap (.H :: cp)).map.node v)
        (cpmap (.H :: cp)).cpring :=
      (Hypermap.isCyclicChain_cpring (G := (cpmap (.H :: cp)).map)
        (x₀ := (cpmap (.H :: cp)).point)).isChain
    rw [hMring3] at hchainM
    rw [(List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchainM).2).1,
      Hypermap.inv_node_node]
  have hkeX : k ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point)
      = h ((cpmap cp).map.node⁻¹ (cpmap cp).point) := by
    rw [← hk.face ((cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point),
      Hypermap.face_edge, hinvM, hh]
  have hnG : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = k (injcpStep CpStep.H cp ((cpmap cp).map.node (cpmap cp).point)) :=
    congr_of_sameCycle hk.face (PointedMap.cface_node_ecpH' (cpmap cp) hp)
  have hKhead : k ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = h ((cpmap cp).map.node (cpmap cp).point) := by rw [hnG, hh]
  have hXnode : k (cpmap (.H :: cp)).point
      = k ((cpmap (.H :: cp)).map.edge
          ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)) :=
    congr_of_sameCycle hk.face (cface_edge_node_ecpH (cpmap cp) hp)
  -- both outer ring edges are contracted, so the two merged faces agree
  have hmem1 : (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
      ∈ (cpmap (.H :: cp)).map.insertE
        (listMask (true :: true :: mr') (cpmap (.H :: cp)).cpring
          ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))) :=
    mem_insertE_self _ (List.mem_append_left _ (by rw [hMring]; exact List.Mem.head _))
  have hmem2 : (cpmap (.H :: cp)).point
      ∈ (cpmap (.H :: cp)).map.insertE
        (listMask (true :: true :: mr') (cpmap (.H :: cp)).cpring
          ++ listMask (false :: false :: false :: mc') (ctrenum (.H :: cp))) :=
    mem_insertE_self _ (List.mem_append_left _
      (by rw [hMring]; exact List.Mem.tail _ (List.Mem.head _)))
  have hE1 := (hk.edge _).mpr hmem1
  have hE2 := (hk.edge _).mpr hmem2
  have hsame : h' ((cpmap cpc₀).map.node (cpmap cpc₀).point)
      = h' ((cpmap cpc₀).map.node⁻¹ (cpmap cpc₀).point) := by
    rw [hnGc, hinvGc, ← hKhead, ← hkeX, ← hE1, ← hXnode, hE2]
  -- the contracted ring is long, so the `A` step drops its first two darts
  have hmask : listMask (mr'.map not) ((cpmap cp).cpring.drop 2) ≠ [] :=
    listMask_not_ne_nil mr' _ hlen hall
  have hGclong : (cpmap cpc₀).Long := by
    rw [PointedMap.long_iff]
    have h1 := congrArg List.length htail
    rw [List.length_map, List.length_map, List.length_drop] at h1
    have h2 : 0 < (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).length := by
      rcases hq : listMask (mr'.map not) ((cpmap cp).cpring.drop 2) with _ | ⟨z, l⟩
      · exact absurd hq hmask
      · simp
    omega
  have hT2 : (listMask ((true :: true :: mr').map not) (cpmap (.H :: cp)).cpring).map k
      = (listMask (mr'.map not) ((cpmap cp).cpring.drop 2)).map h := by
    rw [hMring, show ((true :: true :: mr').map not) = false :: false :: mr'.map not from rfl,
      listMask_false, listMask_false, listMask_map, List.map_map]
    exact List.map_congr_left (fun x _ => (hh x).symm)
  have hAring : (cpmap (.A :: cpc₀)).cpring = (cpmap cpc₀).cpring.drop 2 :=
    PointedMap.cpring_ecpA_of_long (cpmap cpc₀) hGclong
  refine ⟨h', kA_coloring' hcol' hsame, ?_⟩
  rw [hT2, ← htail]
  exact congrArg (fun l => List.map h' l) hAring

/-- **`cfctr` is correct.**  When the contract computation succeeds, every
contract colouring of `cpmap cp` for the contract selected by `mr` and `mc`
restricts to a colouring of the contracted map whose ring trace is the trace of
the ring darts `mr` keeps.  The proof runs through the fourteen step cases
above, following the case tree of `cfctr` itself. -/
theorem cfctr_correct : ∀ {cp : CProg} {mr mc : List Bool} {cpc : CProg},
    mr.length = cprsize cp → mc.length = ctrmsize cp → cfctr cp mr mc = some cpc →
    CfctrSpec cp mr mc cpc := by
  intro cp
  induction cp with
  | nil => intro mr mc cpc _ _ h; simp at h
  | cons s cp ih =>
    intro mr mc cpc hmr hmc h
    cases s with
    | R' => simp [cfctr] at h
    | U => simp [cfctr] at h
    | K => simp [cfctr] at h
    | A => simp [cfctr] at h
    | R i =>
      rw [cfctr_R] at h
      obtain ⟨cpc', h', rfl⟩ := Option.map_eq_some_iff.mp h
      have hlen : (rotrMask i mr).length = cprsize cp := by
        rw [length_rotrMask]
        exact hmr
      refine cfctrSpec_R i _ (rotate_rotrMask i mr) ?_ ?_ (ih hlen hmc h')
      · rw [size_ring_cpmap]
        exact hlen
      · rw [length_rotrMask]
    | Y =>
      cases cp with
      | nil =>
        rw [show cprsize [CpStep.Y] = 3 from rfl, List.length_eq_three] at hmr
        obtain ⟨b₁, b₂, b₃, rfl⟩ := hmr
        rw [cfctr_Y_nil] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hns
          obtain rfl : (if b₁ || b₂ || b₃ then [] else [CpStep.Y]) = cpc := by simpa using h
          exact cfctrSpec_Y_nil b₁ b₂ b₃ mc hns
      | cons t cp =>
        match mr, mc with
        | [], _ => simp [cfctr] at h
        | [_], _ => simp [cfctr] at h
        | _ :: _ :: _, [] => simp [cfctr] at h
        | b₁ :: b₂ :: mr', b₃ :: mc' =>
          rw [cfctr_Y_cons] at h
          split at h
          · exact absurd h (by simp)
          · rename_i hns
            obtain ⟨cpc', h', rfl⟩ := Option.map_eq_some_iff.mp h
            have hlen : (b₃ :: mr').length = cprsize (t :: cp) := by
              simp only [cprsize, List.length_cons] at hmr ⊢
              omega
            have hrec := ih hlen (by simpa using hmc) h'
            have hcfg : ConfigProg (t :: cp) := ConfigProg.of_cfctr h'
            cases b₁ with
            | true =>
              cases b₂ with
              | true => exact (hns (by simp [notSparse])).elim
              | false =>
                cases b₃ with
                | true => exact (hns (by simp [notSparse])).elim
                | false =>
                  exact cfctrSpec_Y_erase (by simp) (Or.inl ⟨rfl, rfl⟩) mr' mc' hrec
            | false =>
              cases b₂ with
              | true =>
                cases b₃ with
                | true => exact (hns (by simp [notSparse])).elim
                | false =>
                  exact cfctrSpec_Y_erase (by simp) (Or.inr ⟨rfl, rfl⟩) mr' mc' hrec
              | false =>
                cases b₃ with
                | true => exact cfctrSpec_Y_U (by simp) mr' mc' hrec
                | false =>
                  exact cfctrSpec_Y_Y (by simp) (cfmap_long hcfg).proper mr' mc' hrec
    | H =>
      match mr, mc with
      | [], _ => simp [cfctr] at h
      | [_], _ => simp [cfctr] at h
      | _ :: _ :: _, [] => simp [cfctr] at h
      | _ :: _ :: _, [_] => simp [cfctr] at h
      | _ :: _ :: _, [_, _] => simp [cfctr] at h
      | b₁ :: b₂ :: mr', b₃ :: b₄ :: b₅ :: mc' =>
        rw [cfctr_H] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hns
          split at h
          · exact absurd h (by simp)
          · rename_i hall
            obtain ⟨cpc', h', rfl⟩ := Option.map_eq_some_iff.mp h
            have hmr' : mr'.length + 2 = cprsize cp := by
              simp only [cprsize, List.length_cons] at hmr
              omega
            have hlen : (b₄ :: b₅ :: mr').length = cprsize cp := by
              simp only [List.length_cons]
              omega
            have hrec := ih hlen (by simpa using hmc) h'
            have hlong : (cpmap cp).Long := cfmap_long (ConfigProg.of_cfctr h')
            have hlenr : mr'.length = ((cpmap cp).cpring.drop 2).length := by
              rw [List.length_drop, size_ring_cpmap]
              omega
            cases b₃ with
            | true =>
              cases b₁ with
              | true => exact (hns (by simp [notSparse])).elim
              | false =>
                cases b₄ with
                | true => exact (hns (by simp [notSparse])).elim
                | false =>
                  cases b₂ with
                  | true => exact (hns (by simp [notSparse])).elim
                  | false =>
                    cases b₅ with
                    | true => exact (hns (by simp [notSparse])).elim
                    | false => exact cfctrSpec_H_crossbar hlong.proper mr' mc' hrec
            | false =>
              cases b₁ with
              | true =>
                cases b₄ with
                | true => exact (hns (by simp [notSparse])).elim
                | false =>
                  cases b₂ with
                  | true =>
                    cases b₅ with
                    | true => exact (hns (by simp [notSparse])).elim
                    | false =>
                      exact cfctrSpec_H_A hlong mr' mc' hlenr
                        (fun hc => hall (by simp [hc])) hrec
                  | false =>
                    cases b₅ with
                    | true => exact cfctrSpec_H_erase1 hlong.proper mr' mc' hrec
                    | false =>
                      exact cfctrSpec_H_K hlong (Or.inl ⟨rfl, rfl⟩) mr' mc' hlenr hrec
              | false =>
                cases b₂ with
                | true =>
                  cases b₅ with
                  | true => exact (hns (by simp [notSparse])).elim
                  | false =>
                    cases b₄ with
                    | true => exact cfctrSpec_H_erase2 hlong.proper mr' mc' hrec
                    | false =>
                      exact cfctrSpec_H_K hlong (Or.inr ⟨rfl, rfl⟩) mr' mc' hlenr hrec
                | false =>
                  cases b₄ with
                  | true =>
                    cases b₅ with
                    | true => exact cfctrSpec_H_U hlong.proper mr' mc' hrec
                    | false =>
                      exact cfctrSpec_H_Y hlong (Or.inl ⟨rfl, rfl⟩) mr' mc' hrec
                  | false =>
                    cases b₅ with
                    | true => exact cfctrSpec_H_Y hlong (Or.inr ⟨rfl, rfl⟩) mr' mc' hrec
                    | false => exact cfctrSpec_H_H hlong mr' mc' hrec

/-! ### The contract is node-simple

`cfctr` also checks that the contract is *sparse*: no two of the E-links it
contracts share a node.  That is what the `notSparse` test at each junction
enforces — a `Y` step creates one new node and an `H` step two, and the test
says that the contract meets each new node at most once. -/

/-- Node-simplicity of a list with a head only depends on the node of the
head. -/
private theorem sparse_cons_congr {D : Type*} [Finite D] {G : Hypermap D} {x x' : D}
    {p : List D} (h : G.CNode x x') (hs : G.Sparse (x :: p)) : G.Sparse (x' :: p) := by
  rw [Hypermap.sparse_cons] at hs ⊢
  exact ⟨fun y hy hc => hs.1 y hy (h.trans hc), hs.2⟩

/-- Iterating `node` on an old dart off the ring commutes with the dart
injection of a step. -/
private theorem pow_node_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg)
    {y : (cpmap cp).Dart} (hy : y ∉ (cpmap cp).cpring) : ∀ n : ℕ,
    ((cpmap (s :: cp)).map.node ^ n) (injcpStep s cp y)
      = injcpStep s cp (((cpmap cp).map.node ^ n) y) := by
  have hoff : ∀ n : ℕ, ((cpmap cp).map.node ^ n) y ∉ (cpmap cp).cpring := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact fun hc => ih (Hypermap.mem_cpring_node_iff.mp hc)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, ← node_injcpStep hs cp (hoff n), pow_succ',
      Equiv.Perm.mul_apply]

/-- The node orbit of an old dart off the ring stays inside the image of the
dart injection of a step. -/
private theorem cnode_image_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg)
    {y : (cpmap cp).Dart} (hy : y ∉ (cpmap cp).cpring) {u : (cpmap (s :: cp)).Dart}
    (h : (cpmap (s :: cp)).map.CNode (injcpStep s cp y) u) :
    ∃ z : (cpmap cp).Dart, u = injcpStep s cp z ∧ (cpmap cp).map.CNode y z := by
  obtain ⟨n, hn⟩ := (sameCycle_iff_exists_pow _ _ _).mp h
  exact ⟨((cpmap cp).map.node ^ n) y, by rw [← hn, pow_node_injcpStep hs cp hy n],
    (sameCycle_iff_exists_pow _ _ _).mpr ⟨n, rfl⟩⟩

/-- A step preserves and reflects the node orbits of old darts off the ring. -/
private theorem cnode_injcpStep_iff {s : CpStep} (hs : s.IsCubic) (cp : CProg)
    {x : (cpmap cp).Dart} (hx : x ∉ (cpmap cp).cpring) (y : (cpmap cp).Dart) :
    (cpmap (s :: cp)).map.CNode (injcpStep s cp x) (injcpStep s cp y)
      ↔ (cpmap cp).map.CNode x y := by
  constructor
  · intro h
    obtain ⟨z, hz, hxz⟩ := cnode_image_injcpStep hs cp hx h
    rwa [← injcpStep_injective s cp hz] at hxz
  · intro h
    obtain ⟨n, hn⟩ := (sameCycle_iff_exists_pow _ _ _).mp h
    exact (sameCycle_iff_exists_pow _ _ _).mpr
      ⟨n, by rw [pow_node_injcpStep hs cp hx n, hn]⟩

/-- A three-cycle of `node` exhausts a node. -/
private theorem cnode_cycle3 {D : Type*} [Finite D] {G : Hypermap D} {a b c u : D}
    (h1 : G.node a = b) (h2 : G.node b = c) (h3 : G.node c = a) (h : G.CNode a u) :
    u = a ∨ u = b ∨ u = c := by
  obtain ⟨n, hn⟩ := (sameCycle_iff_exists_pow _ _ _).mp h
  have key : ∀ m : ℕ, (G.node ^ m) a = a ∨ (G.node ^ m) a = b ∨ (G.node ^ m) a = c := by
    intro m
    induction m with
    | zero => exact Or.inl rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with he | he | he
      · exact Or.inr (Or.inl (by rw [he, h1]))
      · exact Or.inr (Or.inr (by rw [he, h2]))
      · exact Or.inl (by rw [he, h3])
  rw [← hn]
  exact key n

/-- The node map of an `N` step on an old dart that is neither the reference
dart nor two node steps before it. -/
private theorem node_ecpN_icp {D : Type*} [Finite D] [DecidableEq D] (G : Hypermap D)
    (x₀ v : D) (h1 : v ≠ x₀) (h2 : G.node (G.node v) ≠ x₀) :
    (Hypermap.ecpNMap G x₀).node (.icp v) = .icp (G.node v) := by
  rw [Hypermap.ecpNMap_node, Hypermap.ecpNNode_icp, ite_eq_right h1, ite_eq_right h2]

/-- The node map of an `N` step on the dart two node steps before the reference
dart. -/
private theorem node_ecpN_icp_eq {D : Type*} [Finite D] [DecidableEq D] (G : Hypermap D)
    (x₀ v : D) (h1 : v ≠ x₀) (h2 : G.node (G.node v) = x₀) :
    (Hypermap.ecpNMap G x₀).node (.icp v) = .X := by
  rw [Hypermap.ecpNMap_node, Hypermap.ecpNNode_icp, ite_eq_right h1, ite_eq_left h2]

/-- The node map of an `N` step on the image of its reference dart. -/
private theorem node_ecpN_icp_self {D : Type*} [Finite D] [DecidableEq D] (G : Hypermap D)
    (x₀ : D) : (Hypermap.ecpNMap G x₀).node (.icp x₀) = .Xe := by
  rw [Hypermap.ecpNMap_node, Hypermap.ecpNNode_icp, ite_eq_left rfl]

/-- The node map of a `U` step at the dart before the new one. -/
private theorem node_ecpU_icp_node (M : PointedMap) :
    (Hypermap.ecpUMap M.map M.point).node (.icp (M.map.node M.point))
      = (.X : M.ecpU.Dart) := ite_eq_left rfl

/-- **The node cycle of the junction a `Y` step creates**: the foot of the `Y`
and the two darts the junction adds form one node. -/
private theorem node_junction_ecpY (M : PointedMap) :
    M.ecpY.map.node (.Xe : M.ecpY.Dart) = M.icpY (M.map.node M.point)
      ∧ M.ecpY.map.node (M.icpY (M.map.node M.point)) = (.icp .X : M.ecpY.Dart)
      ∧ M.ecpY.map.node (.icp .X : M.ecpY.Dart) = .Xe := by
  have hUX : (Hypermap.ecpUMap M.map M.point).node (.X : M.ecpU.Dart) = .Xe := rfl
  have hUn : (Hypermap.ecpUMap M.map M.point).node (.icp (M.map.node M.point))
      = (.X : M.ecpU.Dart) := node_ecpU_icp_node M
  refine ⟨?_, ?_, ?_⟩
  · have h1 : M.ecpY.map.node (.Xe : M.ecpY.Dart)
        = .icp ((Hypermap.ecpUMap M.map M.point).node⁻¹ (.X : M.ecpU.Dart)) := rfl
    rw [h1, Hypermap.node_inv_ecpU_X]
    rfl
  · have h2 : M.ecpY.map.node (M.icpY (M.map.node M.point))
        = .icp ((Hypermap.ecpUMap M.map M.point).node (.icp (M.map.node M.point))) :=
      node_ecpN_icp (Hypermap.ecpUMap M.map M.point) .X (.icp (M.map.node M.point))
        ((ecpDart_X_ne_icp _).symm) (by rw [hUn, hUX]; exact ecpDart_Xe_ne_X)
    rw [h2, hUn]
  · exact node_ecpN_icp_self (Hypermap.ecpUMap M.map M.point) .X

/-- The node map of a `Y` step at the image of the reference dart: it leads to
the new dart. -/
private theorem node_ecpY_icpY_point (M : PointedMap) (hp : M.Proper) :
    M.ecpY.map.node (M.icpY M.point) = (.X : M.ecpY.Dart) := by
  have e1 : (Hypermap.ecpUMap M.map M.point).node (.icp M.point)
      = .icp (M.map.node M.point) := Hypermap.ecpUNode_icp_of_ne M.map M.point hp
  refine node_ecpN_icp_eq (Hypermap.ecpUMap M.map M.point) .X (.icp M.point)
    ((ecpDart_X_ne_icp _).symm) ?_
  rw [e1, node_ecpU_icp_node M]

/-- **The node cycles of the two junctions an `H` step creates.**  The left foot
and two of the new darts form one node, the right foot and the other two the
other. -/
private theorem node_junction_ecpH (M : PointedMap) (hp : M.Proper) :
    (M.ecpH.map.node (.Xe : M.ecpH.Dart) = M.icpH M.point
        ∧ M.ecpH.map.node (M.icpH M.point) = (.icp .X : M.ecpH.Dart)
        ∧ M.ecpH.map.node (.icp .X : M.ecpH.Dart) = .Xe)
      ∧ (M.ecpH.map.node (M.icpH (M.map.node M.point)) = (.icp (.icp .X) : M.ecpH.Dart)
        ∧ M.ecpH.map.node (.icp (.icp .X) : M.ecpH.Dart) = .icp .Xe
        ∧ M.ecpH.map.node (.icp .Xe : M.ecpH.Dart) = M.icpH (M.map.node M.point)) := by
  obtain ⟨nY2, nY3, nY1⟩ := node_junction_ecpY M
  have nY4 := node_ecpY_icpY_point M hp
  have nY5 : M.ecpY.map.node (.X : M.ecpY.Dart) = .icp .Xe := PointedMap.node_ecpY M
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have e0 : M.ecpY.map.node⁻¹ (.X : M.ecpY.Dart) = M.icpY M.point :=
      Hypermap.node_inv_ecpY_X M.map M.point hp
    have h1 : M.ecpH.map.node (.Xe : M.ecpH.Dart)
        = .icp (M.ecpY.map.node⁻¹ (.X : M.ecpY.Dart)) := rfl
    rw [h1, e0]
    rfl
  · have h2 : M.ecpH.map.node (M.icpH M.point)
        = .icp (M.ecpY.map.node (M.icpY M.point)) :=
      node_ecpN_icp M.ecpY.map .X (M.icpY M.point) ((ecpDart_X_ne_icp _).symm)
        (by rw [nY4, nY5]; exact (ecpDart_X_ne_icp _).symm)
    rw [h2, nY4]
  · exact node_ecpN_icp_self M.ecpY.map .X
  · have h2 : M.ecpH.map.node (M.icpH (M.map.node M.point))
        = .icp (M.ecpY.map.node (M.icpY (M.map.node M.point))) :=
      node_ecpN_icp M.ecpY.map .X (M.icpY (M.map.node M.point)) ((ecpDart_X_ne_icp _).symm)
        (by rw [nY3, nY1]; exact ecpDart_Xe_ne_X)
    rw [h2, nY3]
  · have h2 : M.ecpH.map.node (.icp (.icp .X) : M.ecpH.Dart)
        = .icp (M.ecpY.map.node (.icp .X : M.ecpY.Dart)) :=
      node_ecpN_icp M.ecpY.map .X (.icp .X) ((ecpDart_X_ne_icp _).symm)
        (by rw [nY1, nY2]; exact (ecpDart_X_ne_icp _).symm)
    rw [h2, nY1]
  · have h2 : M.ecpH.map.node (.icp .Xe : M.ecpH.Dart)
        = .icp (M.ecpY.map.node (.Xe : M.ecpY.Dart)) :=
      node_ecpN_icp M.ecpY.map .X .Xe ecpDart_Xe_ne_X
        (by rw [nY2, nY3]; exact (ecpDart_X_ne_icp _).symm)
    rw [h2, nY2]
    rfl

/-- The list whose node-simplicity `cfctr` checks: the E-partners of the ring
darts the ring mask selects, together with the edge closure of the kernel darts
the kernel mask selects. -/
noncomputable def ctrList (cp : CProg) (mr mc : List Bool) : List (cpmap cp).Dart :=
  (listMask mr (cpmap cp).cpring).map (cpmap cp).map.edge
    ++ (cpmap cp).map.insertE (listMask mc (ctrenum cp))

/-- Taking E-partners commutes with the dart injection of a step. -/
private theorem map_edge_map_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg)
    (l : List (cpmap cp).Dart) :
    (l.map (injcpStep s cp)).map (cpmap (s :: cp)).map.edge
      = (l.map (cpmap cp).map.edge).map (injcpStep s cp) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun x _ => (edge_injcpStep hs cp x).symm)

/-- The darts of a node-simple contract lie off the ring, their images under the
dart injection of a step are node-simple, and none of them shares a node with
the new reference dart. -/
private theorem sparse_map_injcpStep {s : CpStep} (hs : s.IsCubic) {cp : CProg}
    {L : List (cpmap cp).Dart}
    (hsp : (cpmap cp).map.Sparse ((cpmap cp).point :: L)) :
    (∀ y ∈ L, y ∉ (cpmap cp).cpring)
      ∧ (cpmap (s :: cp)).map.Sparse (L.map (injcpStep s cp))
      ∧ (∀ y ∈ L, ¬ (cpmap (s :: cp)).map.CNode (cpmap (s :: cp)).point
          (injcpStep s cp y)) := by
  rw [Hypermap.sparse_cons] at hsp
  have hoff : ∀ y ∈ L, y ∉ (cpmap cp).cpring := fun y hy hc =>
    hsp.1 y hy (Hypermap.mem_cpring.mp hc)
  refine ⟨hoff, ?_, ?_⟩
  · simp only [Hypermap.Sparse, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hsp.2
    intro a b ha hb hab hc
    exact hab ((cnode_injcpStep_iff hs cp (hoff a ha) b).mp hc)
  · intro y hy hc
    exact not_mem_cpring_injcpStep hs cp (hoff y hy) (Hypermap.mem_cpring.mpr hc)

/-- **The `R` step of `sparse_cfctr`**: a rotation rotates the ring and the ring
mask, and moves the reference dart along its own node. -/
private theorem sparseCtr_R {cp : CProg} (n : ℕ) {mr m' : List Bool}
    (hm' : m'.rotate n = mr) (hlen : m'.length = (cpmap cp).cpring.length) (mc : List Bool)
    (hIH : (cpmap cp).map.Sparse ((cpmap cp).point :: ctrList cp m' mc)) :
    (cpmap (.R n :: cp)).map.Sparse
      ((cpmap (.R n :: cp)).point :: ctrList (.R n :: cp) mr mc) := by
  have hringR : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
    Hypermap.cpring_ecpR (G := (cpmap cp).map) (x₀ := (cpmap cp).point) n
  have hperm : (listMask mr ((cpmap cp).cpring.rotate n)).Perm
      (listMask m' (cpmap cp).cpring) := by
    rw [← hm']
    exact listMask_rotate_perm m' (cpmap cp).cpring hlen n
  have hp2 : (ctrList (.R n :: cp) mr mc).Perm (ctrList cp m' mc) := by
    simp only [ctrList, hringR, ctrenum_R]
    exact List.Perm.append_right _ (List.Perm.map _ hperm)
  have hpt : (cpmap (.R n :: cp)).point ∈ (cpmap cp).cpring := by
    have h0 : (cpmap (.R n :: cp)).point ∈ (cpmap (.R n :: cp)).cpring :=
      Hypermap.self_mem_cpring
    rw [hringR] at h0
    exact List.mem_rotate.mp h0
  exact sparse_cons_congr (Hypermap.mem_cpring.mp hpt)
    (hIH.perm (List.Perm.cons _ hp2.symm))

/-- **The base `Y` step of `sparse_cfctr`**: the initial `Y` step builds the
three-dart ring, whose three E-partners all lie on the new node, so the contract
may meet at most one of them. -/
private theorem sparseCtr_Y_nil {b₁ b₂ b₃ : Bool} (hns : ¬ notSparse b₁ b₂ b₃ = true)
    (mc : List Bool) :
    (cpmap [CpStep.Y]).map.Sparse
      ((cpmap [CpStep.Y]).point :: ctrList [CpStep.Y] [b₁, b₂, b₃] mc) := by
  have hnodeY : (cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point
      = (EcpDart.icp EcpDart.Xe : (cpmap [CpStep.Y]).Dart) := PointedMap.node_ecpY (cpmap [])
  have hring0 : (cpmap [CpStep.Y]).cpring
      = (cpmap [CpStep.Y]).map.node (cpmap [CpStep.Y]).point :: (cpmap [CpStep.Y]).point
        :: (cpmap ([] : CProg)).cpring.tail.map (injcpStep .Y []) :=
    PointedMap.cpring_ecpY' (cpmap [])
  have hring : (cpmap [CpStep.Y]).cpring
      = ((.icp .Xe : (cpmap [CpStep.Y]).Dart) :: .X :: [.icp (.icp true)]) := by
    rw [hring0, hnodeY,
      show (cpmap ([] : CProg)).cpring = [false, true] from PointedMap.cpring_cpmap0]
    rfl
  have hm1 : (EcpDart.icp (EcpDart.icp false) : EcpDart (EcpDart Bool))
      ∉ [EcpDart.icp EcpDart.Xe, EcpDart.X, EcpDart.icp (EcpDart.icp true)] := by simp
  have hm2 : (EcpDart.Xe : EcpDart (EcpDart Bool))
      ∉ [EcpDart.icp EcpDart.Xe, EcpDart.X, EcpDart.icp (EcpDart.icp true)] := by simp
  have hm3 : (EcpDart.icp EcpDart.X : EcpDart (EcpDart Bool))
      ∉ [EcpDart.icp EcpDart.Xe, EcpDart.X, EcpDart.icp (EcpDart.icp true)] := by simp
  have key : ∀ u : (cpmap [CpStep.Y]).Dart, u ∉ (cpmap [CpStep.Y]).cpring →
      (cpmap [CpStep.Y]).map.Sparse ((cpmap [CpStep.Y]).point :: [u]) := by
    intro u hu
    refine Hypermap.sparse_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact fun hc => hu (Hypermap.mem_cpring.mpr hc)
  have hnil : (cpmap [CpStep.Y]).map.insertE (listMask mc (ctrenum [CpStep.Y])) = [] := by
    rw [ctrenum_Y_nil, listMask_nil_list, Hypermap.insertE_nil]
  cases b₁ <;> cases b₂ <;> cases b₃
  · -- nothing contracted
    have hlist : ctrList [CpStep.Y] [false, false, false] mc = [] := by
      rw [ctrList, hnil, hring]
      rfl
    rw [hlist]
    exact List.pairwise_singleton _ _
  · -- the third ring edge
    have hlist : ctrList [CpStep.Y] [false, false, true] mc
        = [(.icp (.icp false) : (cpmap [CpStep.Y]).Dart)] := by
      rw [ctrList, hnil, hring]
      rfl
    rw [hlist]
    refine key _ ?_
    rw [hring]
    exact hm1
  · -- the second ring edge
    have hlist : ctrList [CpStep.Y] [false, true, false] mc
        = [(.Xe : (cpmap [CpStep.Y]).Dart)] := by
      rw [ctrList, hnil, hring]
      rfl
    rw [hlist]
    refine key _ ?_
    rw [hring]
    exact hm2
  · exact absurd rfl hns
  · -- the first ring edge
    have hlist : ctrList [CpStep.Y] [true, false, false] mc
        = [(.icp .X : (cpmap [CpStep.Y]).Dart)] := by
      rw [ctrList, hnil, hring]
      rfl
    rw [hlist]
    refine key _ ?_
    rw [hring]
    exact hm3
  · exact absurd rfl hns
  · exact absurd rfl hns
  · exact absurd rfl hns

/-- A new dart of a `Y` step is none of the ring darts of the step. -/
private theorem notMem_cons_map_icpY {α : Type*} {u : EcpDart (EcpDart α)}
    (hu : u = .icp .X ∨ u = .Xe) (t : List α) (f : α → EcpDart (EcpDart α))
    (hf : ∀ z, f z = .icp (.icp z)) :
    u ∉ ((.icp .Xe : EcpDart (EcpDart α)) :: .X :: t.map f) := by
  intro hm
  rcases List.mem_cons.mp hm with h | hm
  · rcases hu with rfl | rfl
    · exact (Ne.symm ecpDart_Xe_ne_X) (EcpDart.icp_inj.mp h)
    · exact ecpDart_Xe_ne_icp _ h
  rcases List.mem_cons.mp hm with h | hm
  · rcases hu with rfl | rfl
    · exact (ecpDart_X_ne_icp _).symm h
    · exact ecpDart_Xe_ne_X h
  · obtain ⟨w, -, hweq⟩ := List.mem_map.mp hm
    rw [hf w] at hweq
    rcases hu with rfl | rfl
    · exact (ecpDart_X_ne_icp _).symm (EcpDart.icp_inj.mp hweq)
    · exact ecpDart_Xe_ne_icp _ hweq.symm

/-- The image of an old dart off the tail of the ring is not a ring dart of a
`Y` step. -/
private theorem notMem_cons_map_icpY' {α : Type*} {z : α} {t : List α} (hz : z ∉ t)
    (f : α → EcpDart (EcpDart α)) (hf : ∀ w, f w = .icp (.icp w)) :
    f z ∉ ((.icp .Xe : EcpDart (EcpDart α)) :: .X :: t.map f) := by
  rw [hf z]
  intro hm
  rcases List.mem_cons.mp hm with h | hm
  · exact ecpDart_Xe_ne_icp _ (EcpDart.icp_inj.mp h).symm
  rcases List.mem_cons.mp hm with h | hm
  · exact (ecpDart_X_ne_icp _).symm h
  · obtain ⟨w, hw, hweq⟩ := List.mem_map.mp hm
    rw [hf w] at hweq
    obtain rfl : w = z := EcpDart.icp_inj.mp (EcpDart.icp_inj.mp hweq)
    exact hz hw

/-- **The `Y` step of `sparse_cfctr`**: a `Y` step creates one new node, made of
its foot and the two darts the junction adds; the sparseness test says that the
contract meets that node at most once. -/
private theorem sparseCtr_Y {cp : CProg} (hne : cp ≠ []) {b₁ b₂ b₃ : Bool}
    (hns : ¬ notSparse b₁ b₂ b₃ = true) (mr' mc' : List Bool)
    (hIH : (cpmap cp).map.Sparse ((cpmap cp).point :: ctrList cp (b₃ :: mr') mc')) :
    (cpmap (.Y :: cp)).map.Sparse
      ((cpmap (.Y :: cp)).point :: ctrList (.Y :: cp) (b₁ :: b₂ :: mr') (b₃ :: mc')) := by
  obtain ⟨hoff, hspImg, hXImg⟩ := sparse_map_injcpStep (s := CpStep.Y) trivial hIH
  obtain ⟨t, ht⟩ : ∃ t, (cpmap cp).cpring.tail = t := ⟨_, rfl⟩
  have hGring : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: t := by
    rw [← ht]; exact Hypermap.head_cpring
  have hMring : (cpmap (.Y :: cp)).cpring
      = (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point :: (cpmap (.Y :: cp)).point
        :: t.map (injcpStep .Y cp) := by
    rw [← ht]; exact PointedMap.cpring_ecpY' (cpmap cp)
  have hnX : (cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point
      = (EcpDart.icp EcpDart.Xe : (cpmap (.Y :: cp)).Dart) := PointedMap.node_ecpY (cpmap cp)
  have hpX : (cpmap (.Y :: cp)).point = (EcpDart.X : (cpmap (.Y :: cp)).Dart) := rfl
  have he1 : (cpmap (.Y :: cp)).map.edge ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
      = (EcpDart.icp EcpDart.X : (cpmap (.Y :: cp)).Dart) := by rw [hnX]; rfl
  have he2 : (cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point
      = (EcpDart.Xe : (cpmap (.Y :: cp)).Dart) := rfl
  have hnd : (cpmap cp).map.node (cpmap cp).point ∉ t := by
    have h0 : (cpmap cp).cpring.Nodup := Hypermap.nodup_cpring
    rw [hGring] at h0
    exact (List.nodup_cons.mp h0).1
  have hnotring : ∀ u : (cpmap (.Y :: cp)).Dart, u ∉ (cpmap (.Y :: cp)).cpring →
      ¬ (cpmap (.Y :: cp)).map.CNode (cpmap (.Y :: cp)).point u :=
    fun u hu hc => hu (Hypermap.mem_cpring.mpr hc)
  have hbase : (cpmap (.Y :: cp)).map.Sparse ((cpmap (.Y :: cp)).point
      :: (ctrList cp (b₃ :: mr') mc').map (injcpStep .Y cp)) := by
    refine Hypermap.sparse_cons.mpr ⟨?_, hspImg⟩
    intro v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    exact hXImg y hy
  have key : ∀ n : (cpmap (.Y :: cp)).Dart,
      ¬ (cpmap (.Y :: cp)).map.CNode (cpmap (.Y :: cp)).point n →
      (∀ y ∈ ctrList cp (b₃ :: mr') mc',
        ¬ (cpmap (.Y :: cp)).map.CNode n (injcpStep .Y cp y)) →
      (cpmap (.Y :: cp)).map.Sparse ((cpmap (.Y :: cp)).point
        :: n :: (ctrList cp (b₃ :: mr') mc').map (injcpStep .Y cp)) := by
    intro n h1 h2
    refine Hypermap.sparse_cons.mpr ⟨?_, Hypermap.sparse_cons.mpr ⟨?_, hspImg⟩⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact h1
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
        exact hXImg y hy
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
      exact h2 y hy
  have hnotimg : ∀ u : (cpmap (.Y :: cp)).Dart,
      (∀ z : (cpmap cp).Dart, u ≠ injcpStep .Y cp z) →
      ∀ y ∈ ctrList cp (b₃ :: mr') mc',
        ¬ (cpmap (.Y :: cp)).map.CNode u (injcpStep .Y cp y) := by
    intro u hu y hy hc
    obtain ⟨z, hz, -⟩ := cnode_image_injcpStep (s := CpStep.Y) trivial cp (hoff y hy) hc.symm
    exact hu z hz
  have hnotimg3 : ∀ y ∈ ctrList cp (b₃ :: mr') mc',
      ¬ (cpmap (.Y :: cp)).map.CNode
        (injcpStep .Y cp ((cpmap cp).map.node (cpmap cp).point)) (injcpStep .Y cp y) := by
    intro y hy hc
    have h1 := (cnode_injcpStep_iff (s := CpStep.Y) trivial cp (hoff y hy)
      ((cpmap cp).map.node (cpmap cp).point)).mp hc.symm
    exact hoff y hy (Hypermap.mem_cpring.mpr
      (((cpmap cp).map.cnode_node (cpmap cp).point).trans h1.symm))
  have hd1 : ¬ (cpmap (.Y :: cp)).map.CNode (cpmap (.Y :: cp)).point
      ((cpmap (.Y :: cp)).map.edge ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)) := by
    refine hnotring _ ?_
    rw [he1, hMring, hnX, hpX]
    exact notMem_cons_map_icpY (Or.inl rfl) t (injcpStep .Y cp) (fun _ => rfl)
  have hd2 : ¬ (cpmap (.Y :: cp)).map.CNode (cpmap (.Y :: cp)).point
      ((cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point) := by
    refine hnotring _ ?_
    rw [he2, hMring, hnX, hpX]
    exact notMem_cons_map_icpY (Or.inr rfl) t (injcpStep .Y cp) (fun _ => rfl)
  have hd3 : ¬ (cpmap (.Y :: cp)).map.CNode (cpmap (.Y :: cp)).point
      (injcpStep .Y cp ((cpmap cp).map.node (cpmap cp).point)) := by
    refine hnotring _ ?_
    rw [hMring, hnX, hpX]
    exact notMem_cons_map_icpY' hnd (injcpStep .Y cp) (fun _ => rfl)
  have hd1e : ∀ y ∈ ctrList cp (b₃ :: mr') mc',
      ¬ (cpmap (.Y :: cp)).map.CNode
        ((cpmap (.Y :: cp)).map.edge ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point))
        (injcpStep .Y cp y) := by
    refine hnotimg _ ?_
    intro z hz
    rw [he1] at hz
    have hz2 : (EcpDart.icp EcpDart.X : (cpmap (.Y :: cp)).Dart)
        = EcpDart.icp (EcpDart.icp z) := hz
    exact ecpDart_X_ne_icp _ (EcpDart.icp_inj.mp hz2)
  have hd2e : ∀ y ∈ ctrList cp (b₃ :: mr') mc',
      ¬ (cpmap (.Y :: cp)).map.CNode ((cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point)
        (injcpStep .Y cp y) := by
    refine hnotimg _ ?_
    intro z hz
    rw [he2] at hz
    have hz2 : (EcpDart.Xe : (cpmap (.Y :: cp)).Dart)
        = EcpDart.icp (EcpDart.icp z) := hz
    exact ecpDart_Xe_ne_icp _ hz2
  cases b₁ <;> cases b₂ <;> cases b₃
  · have hlist : ctrList (.Y :: cp) (false :: false :: mr') (false :: mc')
        = (ctrList cp (false :: mr') mc').map (injcpStep .Y cp) := by
      simp only [ctrList, hMring, hGring, ctrenum_Y' cp hne, List.map_cons, listMask_false,
        listMask_map, List.map_append, map_edge_map_injcpStep (s := CpStep.Y) trivial cp,
        insertE_injcpStep (s := CpStep.Y) trivial cp]
    rw [hlist]
    exact hbase
  · have hlist : ctrList (.Y :: cp) (false :: false :: mr') (true :: mc')
        = (((listMask mr' t).map (cpmap cp).map.edge).map (injcpStep .Y cp))
          ++ (injcpStep .Y cp ((cpmap cp).map.node (cpmap cp).point)
            :: injcpStep .Y cp ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
            :: ((cpmap cp).map.insertE (listMask mc' (ctrenum cp))).map
                (injcpStep .Y cp)) := by
      simp only [ctrList, hMring, ctrenum_Y' cp hne, List.map_cons, listMask_false,
        listMask_true, listMask_map, Hypermap.insertE_cons,
        map_edge_map_injcpStep (s := CpStep.Y) trivial cp,
        insertE_injcpStep (s := CpStep.Y) trivial cp,
        ← edge_injcpStep (s := CpStep.Y) trivial cp]
    have hIMG : (ctrList cp (true :: mr') mc').map (injcpStep .Y cp)
        = injcpStep .Y cp ((cpmap cp).map.edge ((cpmap cp).map.node (cpmap cp).point))
          :: ((((listMask mr' t).map (cpmap cp).map.edge).map (injcpStep .Y cp))
            ++ ((cpmap cp).map.insertE (listMask mc' (ctrenum cp))).map
                (injcpStep .Y cp)) := by
      simp only [ctrList, hGring, listMask_true, List.map_cons, List.map_append,
        List.cons_append]
    refine (key _ hd3 hnotimg3).perm (List.Perm.cons _ ?_)
    rw [hlist, hIMG]
    exact (List.perm_middle.trans (List.Perm.cons _ List.perm_middle)).symm
  · have hlist : ctrList (.Y :: cp) (false :: true :: mr') (false :: mc')
        = (cpmap (.Y :: cp)).map.edge (cpmap (.Y :: cp)).point
          :: (ctrList cp (false :: mr') mc').map (injcpStep .Y cp) := by
      simp only [ctrList, hMring, hGring, ctrenum_Y' cp hne, List.map_cons, listMask_false,
        listMask_true, listMask_map, List.map_append, List.cons_append,
        map_edge_map_injcpStep (s := CpStep.Y) trivial cp,
        insertE_injcpStep (s := CpStep.Y) trivial cp]
    rw [hlist]
    exact key _ hd2 hd2e
  · exact absurd rfl hns
  · have hlist : ctrList (.Y :: cp) (true :: false :: mr') (false :: mc')
        = (cpmap (.Y :: cp)).map.edge
            ((cpmap (.Y :: cp)).map.node (cpmap (.Y :: cp)).point)
          :: (ctrList cp (false :: mr') mc').map (injcpStep .Y cp) := by
      simp only [ctrList, hMring, hGring, ctrenum_Y' cp hne, List.map_cons, listMask_false,
        listMask_true, listMask_map, List.map_append, List.cons_append,
        map_edge_map_injcpStep (s := CpStep.Y) trivial cp,
        insertE_injcpStep (s := CpStep.Y) trivial cp]
    rw [hlist]
    exact key _ hd1 hd1e
  · exact absurd rfl hns
  · exact absurd rfl hns
  · exact absurd rfl hns

/-- Swapping the first block of a concatenation with the second. -/
private theorem perm_append_left_comm {α : Type*} (l₁ l₂ l₃ : List α) :
    (l₁ ++ (l₂ ++ l₃)).Perm (l₂ ++ (l₁ ++ l₃)) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right l₃ List.perm_append_comm

/-- Moving the first block of a fivefold concatenation past the next three. -/
private theorem perm_move_block {α : Type*} (q p₂ p₃ q₃ r : List α) :
    (q ++ (p₂ ++ (p₃ ++ (q₃ ++ r)))).Perm (p₂ ++ (p₃ ++ (q₃ ++ (q ++ r)))) :=
  (perm_append_left_comm q p₂ _).trans (List.Perm.append_left p₂
    ((perm_append_left_comm q p₃ _).trans (List.Perm.append_left p₃
      (perm_append_left_comm q q₃ r))))

/-- The edge closure of a list is a permutation of the list together with the
E-partners of its darts. -/
private theorem insertE_perm_append {D : Type*} (G : Hypermap D) :
    ∀ p : List D, (G.insertE p).Perm (p ++ p.map G.edge) := by
  intro p
  induction p with
  | nil => exact List.Perm.refl _
  | cons x p ih =>
    rw [Hypermap.insertE_cons, List.map_cons, List.cons_append]
    refine List.Perm.cons x ?_
    exact ((List.Perm.cons _ ih).trans (List.perm_middle (a := G.edge x)).symm)

/-- A new dart of an `H` step is none of the ring darts of the step. -/
private theorem notMem_cpring_newH {α : Type*} {u : EcpDart (EcpDart (EcpDart α))}
    (hu : u = .icp (.icp .X) ∨ u = .Xe ∨ u = .icp .X ∨ u = .icp .Xe)
    (t : List α) (f : α → EcpDart (EcpDart (EcpDart α)))
    (hf : ∀ z, f z = .icp (.icp (.icp z))) :
    u ∉ ((.icp (.icp .Xe) : EcpDart (EcpDart (EcpDart α))) :: .X :: t.map f) := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp [hf]

/-- The image of an old dart off the tail of the ring is not a ring dart of an
`H` step. -/
private theorem notMem_cpring_newH' {α : Type*} {z : α} {t : List α} (hz : z ∉ t)
    (f : α → EcpDart (EcpDart (EcpDart α))) (hf : ∀ w, f w = .icp (.icp (.icp w))) :
    f z ∉ ((.icp (.icp .Xe) : EcpDart (EcpDart (EcpDart α))) :: .X :: t.map f) := by
  simp only [hf, List.mem_cons, List.mem_map, not_or]
  refine ⟨by simp, by simp, ?_⟩
  rintro ⟨w, hw, hweq⟩
  obtain rfl : w = z :=
    EcpDart.icp_inj.mp (EcpDart.icp_inj.mp (EcpDart.icp_inj.mp hweq))
  exact hz hw

/-- **The `H` step of `sparse_cfctr`**: an `H` step creates two new nodes, each
made of one foot of the junction and two of the darts it adds; the sparseness
test says that the contract meets each of them at most once. -/
private theorem sparseCtr_H {cp : CProg} (hprop : (cpmap cp).Proper)
    {b₁ b₂ b₃ b₄ b₅ : Bool}
    (hns : ¬ (notSparse b₃ b₁ b₄ || notSparse b₃ b₂ b₅) = true)
    (mr' mc' : List Bool)
    (hIH : (cpmap cp).map.Sparse ((cpmap cp).point :: ctrList cp (b₄ :: b₅ :: mr') mc')) :
    (cpmap (.H :: cp)).map.Sparse
      ((cpmap (.H :: cp)).point
        :: ctrList (.H :: cp) (b₁ :: b₂ :: mr') (b₃ :: b₄ :: b₅ :: mc')) := by
  obtain ⟨hoff, hspImg, hXImg⟩ := sparse_map_injcpStep (s := CpStep.H) trivial hIH
  obtain ⟨d, hd⟩ : ∃ d, (cpmap cp).cpring.drop 2 = d := ⟨_, rfl⟩
  have hGring : (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: d := by
    rw [← hd]; exact Hypermap.head_proper_cpring hprop
  have hMring : (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point :: (cpmap (.H :: cp)).point
        :: d.map (injcpStep .H cp) := by
    rw [← hd]; exact PointedMap.cpring_ecpH' (cpmap cp) hprop
  have hnX : (cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point
      = (EcpDart.icp (EcpDart.icp EcpDart.Xe) : (cpmap (.H :: cp)).Dart) :=
    PointedMap.node_ecpH (cpmap cp) hprop
  have hpX : (cpmap (.H :: cp)).point = (EcpDart.X : (cpmap (.H :: cp)).Dart) := rfl
  have hfX : (cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point
      = (EcpDart.icp EcpDart.X : (cpmap (.H :: cp)).Dart) := rfl
  have he1 : (cpmap (.H :: cp)).map.edge ((cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point)
      = (EcpDart.icp (EcpDart.icp EcpDart.X) : (cpmap (.H :: cp)).Dart) := by rw [hnX]; rfl
  have he2 : (cpmap (.H :: cp)).map.edge (cpmap (.H :: cp)).point
      = (EcpDart.Xe : (cpmap (.H :: cp)).Dart) := rfl
  have he3 : (cpmap (.H :: cp)).map.edge
      ((cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point)
      = (EcpDart.icp EcpDart.Xe : (cpmap (.H :: cp)).Dart) := rfl
  have hnodup : (cpmap cp).cpring.Nodup := Hypermap.nodup_cpring
  rw [hGring] at hnodup
  have hnd1 : (cpmap cp).map.node (cpmap cp).point ∉ d :=
    fun hc => (List.nodup_cons.mp hnodup).1 (List.Mem.tail _ hc)
  have hnd2 : (cpmap cp).point ∉ d :=
    (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
  -- the new darts do not lie on the ring of the step
  have hnotring : ∀ u : (cpmap (.H :: cp)).Dart, u ∉ (cpmap (.H :: cp)).cpring →
      ¬ (cpmap (.H :: cp)).map.CNode (cpmap (.H :: cp)).point u :=
    fun u hu hc => hu (Hypermap.mem_cpring.mpr hc)
  have hnew1 : ∀ u : (cpmap (.H :: cp)).Dart,
      (u = .icp (.icp .X) ∨ u = .Xe ∨ u = .icp .X ∨ u = .icp .Xe) →
      ¬ (cpmap (.H :: cp)).map.CNode (cpmap (.H :: cp)).point u := by
    intro u hu
    refine hnotring u ?_
    rw [hMring, hnX, hpX]
    exact notMem_cpring_newH hu d (injcpStep .H cp) (fun _ => rfl)
  have hnew2 : ∀ z : (cpmap cp).Dart, z ∉ d →
      ¬ (cpmap (.H :: cp)).map.CNode (cpmap (.H :: cp)).point (injcpStep .H cp z) := by
    intro z hz
    refine hnotring _ ?_
    rw [hMring, hnX, hpX]
    exact notMem_cpring_newH' hz (injcpStep .H cp) (fun _ => rfl)
  -- the new darts share no node with the image of the contract below
  have hnotimg : ∀ u : (cpmap (.H :: cp)).Dart,
      (∀ z : (cpmap cp).Dart, u ≠ injcpStep .H cp z) →
      ∀ y ∈ ctrList cp (b₄ :: b₅ :: mr') mc',
        ¬ (cpmap (.H :: cp)).map.CNode u (injcpStep .H cp y) := by
    intro u hu y hy hc
    obtain ⟨z, hz, -⟩ := cnode_image_injcpStep (s := CpStep.H) trivial cp (hoff y hy) hc.symm
    exact hu z hz
  have hnewimg : ∀ u : (cpmap (.H :: cp)).Dart,
      (u = .icp (.icp .X) ∨ u = .Xe ∨ u = .icp .X ∨ u = .icp .Xe) →
      ∀ y ∈ ctrList cp (b₄ :: b₅ :: mr') mc',
        ¬ (cpmap (.H :: cp)).map.CNode u (injcpStep .H cp y) := by
    intro u hu
    refine hnotimg u ?_
    intro z hz
    rcases hu with rfl | rfl | rfl | rfl
    · have hz2 : (EcpDart.icp (EcpDart.icp EcpDart.X) : (cpmap (.H :: cp)).Dart)
          = EcpDart.icp (EcpDart.icp (EcpDart.icp z)) := hz
      exact ecpDart_X_ne_icp z (EcpDart.icp_inj.mp (EcpDart.icp_inj.mp hz2))
    · have hz2 : (EcpDart.Xe : (cpmap (.H :: cp)).Dart)
          = EcpDart.icp (EcpDart.icp (EcpDart.icp z)) := hz
      exact ecpDart_Xe_ne_icp _ hz2
    · have hz2 : (EcpDart.icp EcpDart.X : (cpmap (.H :: cp)).Dart)
          = EcpDart.icp (EcpDart.icp (EcpDart.icp z)) := hz
      exact ecpDart_X_ne_icp _ (EcpDart.icp_inj.mp hz2)
    · have hz2 : (EcpDart.icp EcpDart.Xe : (cpmap (.H :: cp)).Dart)
          = EcpDart.icp (EcpDart.icp (EcpDart.icp z)) := hz
      exact ecpDart_Xe_ne_icp _ (EcpDart.icp_inj.mp hz2)
  have hnotimg2 : ∀ x : (cpmap cp).Dart, x ∈ (cpmap cp).cpring →
      ∀ y ∈ ctrList cp (b₄ :: b₅ :: mr') mc',
        ¬ (cpmap (.H :: cp)).map.CNode (injcpStep .H cp x) (injcpStep .H cp y) := by
    intro x hx y hy hc
    have h1 := (cnode_injcpStep_iff (s := CpStep.H) trivial cp (hoff y hy) x).mp hc.symm
    exact hoff y hy (Hypermap.mem_cpring.mpr ((Hypermap.mem_cpring.mp hx).trans h1.symm))
  -- the two new nodes
  obtain ⟨-, A1, A2, A3⟩ := node_junction_ecpH (cpmap cp) hprop
  have A1' : (cpmap (.H :: cp)).map.node
      (injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point))
      = (EcpDart.icp (EcpDart.icp EcpDart.X) : (cpmap (.H :: cp)).Dart) := A1
  have A2' : (cpmap (.H :: cp)).map.node
      (EcpDart.icp (EcpDart.icp EcpDart.X) : (cpmap (.H :: cp)).Dart)
      = EcpDart.icp EcpDart.Xe := A2
  have A3' : (cpmap (.H :: cp)).map.node
      (EcpDart.icp EcpDart.Xe : (cpmap (.H :: cp)).Dart)
      = injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point) := A3
  have hAcl : ∀ u : (cpmap (.H :: cp)).Dart,
      (cpmap (.H :: cp)).map.CNode
          (injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point)) u →
      u = injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point)
        ∨ u = .icp (.icp .X) ∨ u = .icp .Xe := fun _ => cnode_cycle3 A1' A2' A3'
  have hAmem : ∀ a : (cpmap (.H :: cp)).Dart,
      (a = .icp (.icp .X) ∨ a = .icp .Xe
        ∨ a = injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point)) →
      (cpmap (.H :: cp)).map.CNode
        (injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point)) a := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · rw [← A1']; exact (cpmap (.H :: cp)).map.cnode_node _
    · have h0 := ((cpmap (.H :: cp)).map.cnode_node
        (injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point))).trans
        ((cpmap (.H :: cp)).map.cnode_node
          ((cpmap (.H :: cp)).map.node
            (injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point))))
      rwa [A1', A2'] at h0
    · exact Equiv.Perm.SameCycle.refl _ _
  have hAB : ∀ a b : (cpmap (.H :: cp)).Dart,
      (a = .icp (.icp .X) ∨ a = .icp .Xe
        ∨ a = injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point)) →
      (b = .Xe ∨ b = .icp .X ∨ b = injcpStep .H cp (cpmap cp).point) →
      ¬ (cpmap (.H :: cp)).map.CNode a b := by
    intro a b ha hb hc
    have h1 := hAcl b ((hAmem a ha).trans hc)
    rcases hb with rfl | rfl | rfl
    · rcases h1 with h | h | h
      · exact ecpDart_Xe_ne_icp _ h
      · exact ecpDart_Xe_ne_icp _ h
      · exact ecpDart_Xe_ne_icp _ h
    · rcases h1 with h | h | h
      · have h2 : (EcpDart.icp EcpDart.X : (cpmap (.H :: cp)).Dart)
            = EcpDart.icp (EcpDart.icp (EcpDart.icp
              ((cpmap cp).map.node (cpmap cp).point))) := h
        exact ecpDart_X_ne_icp _ (EcpDart.icp_inj.mp h2)
      · exact ecpDart_X_ne_icp _ (EcpDart.icp_inj.mp h)
      · exact (Ne.symm ecpDart_Xe_ne_X) (EcpDart.icp_inj.mp h)
    · rcases h1 with h | h | h
      · exact hprop (injcpStep_injective CpStep.H cp h)
      · have h2 : (EcpDart.icp (EcpDart.icp (EcpDart.icp (cpmap cp).point)) :
            (cpmap (.H :: cp)).Dart) = EcpDart.icp (EcpDart.icp EcpDart.X) := h
        exact (ecpDart_X_ne_icp _).symm (EcpDart.icp_inj.mp (EcpDart.icp_inj.mp h2))
      · have h2 : (EcpDart.icp (EcpDart.icp (EcpDart.icp (cpmap cp).point)) :
            (cpmap (.H :: cp)).Dart) = EcpDart.icp EcpDart.Xe := h
        exact (ecpDart_Xe_ne_icp _) (EcpDart.icp_inj.mp h2).symm
  -- the contract of the step, split into the new darts and the image below
  have hctrH : ctrenum (.H :: cp)
      = [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point]
        ++ (([(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point].map (injcpStep .H cp))
          ++ (ctrenum cp).map (injcpStep .H cp)) := by
    rw [ctrenum_H, ← List.map_append]
    rfl
  have hmaskR : listMask (b₁ :: b₂ :: mr') (cpmap (.H :: cp)).cpring
      = listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
          (cpmap (.H :: cp)).point]
        ++ listMask mr' (d.map (injcpStep .H cp)) := by
    rw [hMring]
    exact listMask_append [b₁, b₂]
      [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point, (cpmap (.H :: cp)).point] rfl
      mr' (d.map (injcpStep .H cp))
  have hmaskK : listMask (b₃ :: b₄ :: b₅ :: mc') (ctrenum (.H :: cp))
      = listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point]
        ++ (listMask [b₄, b₅] ([(cpmap cp).map.node (cpmap cp).point,
              (cpmap cp).point].map (injcpStep .H cp))
          ++ listMask mc' ((ctrenum cp).map (injcpStep .H cp))) := by
    have h1 := listMask_append [b₃]
      [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point] rfl ([b₄, b₅] ++ mc')
      (([(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point].map (injcpStep .H cp))
        ++ (ctrenum cp).map (injcpStep .H cp))
    have h2 := listMask_append [b₄, b₅]
      ([(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point].map (injcpStep .H cp)) rfl
      mc' ((ctrenum cp).map (injcpStep .H cp))
    rw [hctrH]
    exact h1.trans (congrArg (fun l => listMask [b₃]
      [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point] ++ l) h2)
  have hmaskG : listMask (b₄ :: b₅ :: mr') (cpmap cp).cpring
      = listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point]
        ++ listMask mr' d := by
    rw [hGring]
    exact listMask_append [b₄, b₅]
      [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point] rfl mr' d
  have hdec : ctrList (.H :: cp) (b₁ :: b₂ :: mr') (b₃ :: b₄ :: b₅ :: mc')
      = ((listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
            (cpmap (.H :: cp)).point]).map (cpmap (.H :: cp)).map.edge
          ++ ((listMask mr' d).map (cpmap cp).map.edge).map (injcpStep .H cp))
        ++ ((cpmap (.H :: cp)).map.insertE
              (listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point])
            ++ (((cpmap cp).map.insertE (listMask [b₄, b₅]
                [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point])).map
                  (injcpStep .H cp)
              ++ ((cpmap cp).map.insertE (listMask mc' (ctrenum cp))).map
                  (injcpStep .H cp))) := by
    rw [ctrList, hmaskR, hmaskK, List.map_append, Hypermap.insertE_append,
      Hypermap.insertE_append, listMask_map, listMask_map, listMask_map,
      map_edge_map_injcpStep (s := CpStep.H) trivial cp,
      insertE_injcpStep (s := CpStep.H) trivial cp,
      insertE_injcpStep (s := CpStep.H) trivial cp]
  have hIMG : (ctrList cp (b₄ :: b₅ :: mr') mc').map (injcpStep .H cp)
      = (((listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
            (cpmap cp).point]).map (cpmap cp).map.edge).map (injcpStep .H cp))
        ++ ((((listMask mr' d).map (cpmap cp).map.edge).map (injcpStep .H cp))
          ++ ((cpmap cp).map.insertE (listMask mc' (ctrenum cp))).map (injcpStep .H cp)) := by
    rw [ctrList, hmaskG, List.map_append, List.map_append, List.map_append, List.append_assoc]
  have hP3 : (((cpmap cp).map.insertE (listMask [b₄, b₅]
        [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point])).map
          (injcpStep .H cp)).Perm
      ((listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
          (cpmap cp).point]).map (injcpStep .H cp)
        ++ (((listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
            (cpmap cp).point]).map (cpmap cp).map.edge).map (injcpStep .H cp))) := by
    have h0 := List.Perm.map (injcpStep .H cp) (insertE_perm_append (cpmap cp).map
      (listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point, (cpmap cp).point]))
    rwa [List.map_append] at h0
  -- the new darts of the step
  have hNmem : ∀ n ∈ ((listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
          (cpmap (.H :: cp)).point]).map (cpmap (.H :: cp)).map.edge
        ++ ((cpmap (.H :: cp)).map.insertE
            (listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point])
          ++ (listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
              (cpmap cp).point]).map (injcpStep .H cp))),
      (n = .icp (.icp .X) ∨ n = .Xe ∨ n = .icp .X ∨ n = .icp .Xe)
        ∨ (n = injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point)
          ∨ n = injcpStep .H cp (cpmap cp).point) := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
      have hw2 := mem_of_mem_listMask [b₁, b₂] _ hw
      rcases List.mem_cons.mp hw2 with rfl | hw3
      · exact Or.inl (Or.inl he1)
      · rcases List.mem_cons.mp hw3 with rfl | hw4
        · exact Or.inl (Or.inr (Or.inl he2))
        · cases hw4
    rcases List.mem_append.mp hn with hn | hn
    · have h0 : n ∈ (cpmap (.H :: cp)).map.insertE
          [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point] :=
        insertE_mono _ (fun y hy => mem_of_mem_listMask [b₃] _ hy) hn
      rw [Hypermap.insertE_cons, Hypermap.insertE_nil] at h0
      rcases List.mem_cons.mp h0 with rfl | h1
      · exact Or.inl (Or.inr (Or.inr (Or.inl hfX)))
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact Or.inl (Or.inr (Or.inr (Or.inr he3)))
        · cases h2
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
      have hw2 := mem_of_mem_listMask [b₄, b₅] _ hw
      rcases List.mem_cons.mp hw2 with rfl | hw3
      · exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.mp hw3 with rfl | hw4
        · exact Or.inr (Or.inr rfl)
        · cases hw4
  have hN1 : ∀ n ∈ ((listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
          (cpmap (.H :: cp)).point]).map (cpmap (.H :: cp)).map.edge
        ++ ((cpmap (.H :: cp)).map.insertE
            (listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point])
          ++ (listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
              (cpmap cp).point]).map (injcpStep .H cp))),
      ¬ (cpmap (.H :: cp)).map.CNode (cpmap (.H :: cp)).point n := by
    intro n hn
    rcases hNmem n hn with h | h
    · exact hnew1 n h
    · rcases h with rfl | rfl
      · exact hnew2 _ hnd1
      · exact hnew2 _ hnd2
  have hN3 : ∀ n ∈ ((listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
          (cpmap (.H :: cp)).point]).map (cpmap (.H :: cp)).map.edge
        ++ ((cpmap (.H :: cp)).map.insertE
            (listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point])
          ++ (listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
              (cpmap cp).point]).map (injcpStep .H cp))),
      ∀ y ∈ ctrList cp (b₄ :: b₅ :: mr') mc',
      ¬ (cpmap (.H :: cp)).map.CNode n (injcpStep .H cp y) := by
    intro n hn
    rcases hNmem n hn with h | h
    · exact hnewimg n h
    · rcases h with rfl | rfl
      · exact hnotimg2 _ Hypermap.node_mem_cpring
      · exact hnotimg2 _ Hypermap.self_mem_cpring
  have hs2 : ∀ a b : (cpmap (.H :: cp)).Dart, ¬ (cpmap (.H :: cp)).map.CNode a b →
      (cpmap (.H :: cp)).map.Sparse [a, b] := by
    intro a b h
    refine Hypermap.sparse_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact h
  have hN2 : (cpmap (.H :: cp)).map.Sparse
      ((listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
          (cpmap (.H :: cp)).point]).map (cpmap (.H :: cp)).map.edge
        ++ ((cpmap (.H :: cp)).map.insertE
            (listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point])
          ++ (listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
              (cpmap cp).point]).map (injcpStep .H cp))) := by
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;>
      first
        | exact absurd rfl hns
        | simp only [listMask, List.map_cons, List.map_nil, Hypermap.insertE_nil,
            Hypermap.insertE_cons, List.nil_append, List.cons_append, List.append_nil]
    all_goals first
      | exact List.Pairwise.nil
      | exact List.pairwise_singleton _ _
      | exact hs2 _ _ (hAB _ _ (Or.inl he1) (Or.inl he2))
      | exact hs2 _ _ (hAB _ _ (Or.inl he1) (Or.inr (Or.inr rfl)))
      | exact hs2 _ _ (hAB _ _ (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)))
      | exact hs2 _ _ (fun hc => hAB _ _ (Or.inr (Or.inr rfl)) (Or.inl he2) hc.symm)
      | exact hs2 _ _ (fun hc => hAB _ _ (Or.inr (Or.inl he3)) (Or.inr (Or.inl hfX)) hc.symm)
  -- the colouring of the contract of the step
  have key : ∀ N : List (cpmap (.H :: cp)).Dart,
      (∀ n ∈ N, ¬ (cpmap (.H :: cp)).map.CNode (cpmap (.H :: cp)).point n) →
      (cpmap (.H :: cp)).map.Sparse N →
      (∀ n ∈ N, ∀ y ∈ ctrList cp (b₄ :: b₅ :: mr') mc',
        ¬ (cpmap (.H :: cp)).map.CNode n (injcpStep .H cp y)) →
      (cpmap (.H :: cp)).map.Sparse ((cpmap (.H :: cp)).point
        :: (N ++ (ctrList cp (b₄ :: b₅ :: mr') mc').map (injcpStep .H cp))) := by
    intro N h1 h2 h3
    refine Hypermap.sparse_cons.mpr ⟨?_, ?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h1 v hv
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
        exact hXImg y hy
    · refine List.pairwise_append.mpr ⟨h2, hspImg, ?_⟩
      intro a ha b hb
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      exact h3 a ha y hy
  have hperm : (ctrList (.H :: cp) (b₁ :: b₂ :: mr') (b₃ :: b₄ :: b₅ :: mc')).Perm
      (((listMask [b₁, b₂] [(cpmap (.H :: cp)).map.node (cpmap (.H :: cp)).point,
            (cpmap (.H :: cp)).point]).map (cpmap (.H :: cp)).map.edge
          ++ ((cpmap (.H :: cp)).map.insertE
              (listMask [b₃] [(cpmap (.H :: cp)).map.face (cpmap (.H :: cp)).point])
            ++ (listMask [b₄, b₅] [(cpmap cp).map.node (cpmap cp).point,
                (cpmap cp).point]).map (injcpStep .H cp)))
        ++ (ctrList cp (b₄ :: b₅ :: mr') mc').map (injcpStep .H cp)) := by
    rw [hdec, hIMG]
    refine (List.Perm.append_left _ (List.Perm.append_left _
      (List.Perm.append_right _ hP3))).trans ?_
    simp only [List.append_assoc]
    exact List.Perm.append_left _ (perm_move_block _ _ _ _ _)
  exact (key _ hN1 hN2 hN3).perm (List.Perm.cons _ hperm.symm)

/-- **The contract `cfctr` accepts is node-simple.**  Together with the
reference dart, the E-partners of the ring darts the ring mask selects and the
edge closure of the kernel darts the kernel mask selects have pairwise distinct
nodes.  This is what the `notSparse` test at each junction buys, and it is the
`sparse` half of `Hypermap.ValidContract`. -/
theorem sparse_cfctr : ∀ {cp : CProg} {mr mc : List Bool} {cpc : CProg},
    mr.length = cprsize cp → mc.length = ctrmsize cp → cfctr cp mr mc = some cpc →
    (cpmap cp).map.Sparse ((cpmap cp).point :: ctrList cp mr mc) := by
  intro cp
  induction cp with
  | nil => intro mr mc cpc _ _ h; simp at h
  | cons s cp ih =>
    intro mr mc cpc hmr hmc h
    cases s with
    | R' => simp [cfctr] at h
    | U => simp [cfctr] at h
    | K => simp [cfctr] at h
    | A => simp [cfctr] at h
    | R i =>
      rw [cfctr_R] at h
      obtain ⟨cpc', h', -⟩ := Option.map_eq_some_iff.mp h
      have hlen : (rotrMask i mr).length = cprsize cp := by
        rw [length_rotrMask]
        exact hmr
      refine sparseCtr_R i (rotate_rotrMask i mr) ?_ mc (ih hlen hmc h')
      rw [size_ring_cpmap]
      exact hlen
    | Y =>
      cases cp with
      | nil =>
        rw [show cprsize [CpStep.Y] = 3 from rfl, List.length_eq_three] at hmr
        obtain ⟨b₁, b₂, b₃, rfl⟩ := hmr
        rw [cfctr_Y_nil] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hns
          exact sparseCtr_Y_nil hns mc
      | cons t cp =>
        match mr, mc with
        | [], _ => simp [cfctr] at h
        | [_], _ => simp [cfctr] at h
        | _ :: _ :: _, [] => simp [cfctr] at h
        | b₁ :: b₂ :: mr', b₃ :: mc' =>
          rw [cfctr_Y_cons] at h
          split at h
          · exact absurd h (by simp)
          · rename_i hns
            obtain ⟨cpc', h', -⟩ := Option.map_eq_some_iff.mp h
            have hlen : (b₃ :: mr').length = cprsize (t :: cp) := by
              simp only [cprsize, List.length_cons] at hmr ⊢
              omega
            exact sparseCtr_Y (by simp) hns mr' mc' (ih hlen (by simpa using hmc) h')
    | H =>
      match mr, mc with
      | [], _ => simp [cfctr] at h
      | [_], _ => simp [cfctr] at h
      | _ :: _ :: _, [] => simp [cfctr] at h
      | _ :: _ :: _, [_] => simp [cfctr] at h
      | _ :: _ :: _, [_, _] => simp [cfctr] at h
      | b₁ :: b₂ :: mr', b₃ :: b₄ :: b₅ :: mc' =>
        rw [cfctr_H] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hns
          split at h
          · exact absurd h (by simp)
          · obtain ⟨cpc', h', -⟩ := Option.map_eq_some_iff.mp h
            have hlen : (b₄ :: b₅ :: mr').length = cprsize cp := by
              simp only [cprsize, List.length_cons] at hmr ⊢
              omega
            have hprop : (cpmap cp).Proper := (cfmap_long (ConfigProg.of_cfctr h')).proper
            exact sparseCtr_H hprop hns mr' mc' (ih hlen (by simpa using hmc) h')

/-- The contracted map of a top-level call keeps the whole ring: the ring mask
of a top-level call erases no ring edge. -/
theorem cprsize_cfctr_replicate {cp cpc : CProg} {mc : List Bool}
    (hmc : mc.length = ctrmsize cp)
    (h : cfctr cp (List.replicate (cprsize cp) false) mc = some cpc) :
    cprsize cpc = cprsize cp := by
  simpa using cprsize_cfctr (by simp) hmc h

/-! ### The contract of a configuration

The validity of a contract is checked on its mask: a contract must have one to
four edges, and a contract of four edges must leave a triad — a kernel face
adjacent to three of the faces met by the contract, and to one face they miss.
The triad search uses the adjacency mask computation `cpadj` of
`FourColor.CfMap`. -/

/-- The number of darts a mask selects, when it is as long as the list it
selects from. -/
private theorem length_listMask {α : Type*} : ∀ {m : List Bool} {l : List α}, m.length = l.length →
    (listMask m l).length = m.count true := by
  intro m
  induction m with
  | nil => intro l _; rfl
  | cons b m ih =>
    intro l hl
    match l, hl with
    | x :: l, hl =>
      have hl' : m.length = l.length := by simpa using hl
      cases b
      · simp [listMask, ih hl']
      · simp [listMask, ih hl']

/-- The kernel of `cpmap cp` has a triad of index less than `i` for the contract
whose band is `ccm`: a face that is adjacent to at least three of the faces
selected by `ccm`, and to at least one face outside it. -/
def cptriad (ccm : CfMask) (cp : CProg) : ℕ → Bool
  | 0 => false
  | i + 1 =>
      let mt := cpadj (cfmask1 cp i) cp
      let mct := listMask ccm.ring mt.ring ++ listMask ccm.kernel mt.kernel
      (mct.contains false && decide (3 ≤ mct.count true)) || cptriad ccm cp i

/-- The contract represented by the mask `cm` is valid for `cp`: it selects one
to four edges, and four only if the kernel has a triad for its band. -/
def validCtrm (cm : List Bool) (cp : CProg) : Bool :=
  if cm.count true = 4 then cptriad (ctrband cp cm) cp (cpksize cp)
  else decide (0 < cm.count true ∧ cm.count true ≤ 3)

/-- A valid contract is nonempty. -/
theorem count_pos_of_validCtrm {cm : List Bool} {cp : CProg} (h : validCtrm cm cp) :
    0 < cm.count true := by
  rw [validCtrm] at h
  split at h
  · omega
  · rw [decide_eq_true_eq] at h; exact h.1

/-- A valid contract has at most four edges. -/
theorem count_le_four_of_validCtrm {cm : List Bool} {cp : CProg}
    (h : validCtrm cm cp) : cm.count true ≤ 4 := by
  rw [validCtrm] at h
  split at h
  · omega
  · rw [decide_eq_true_eq] at h; omega

/-- The contract mask of a configuration: the mask of the kernel edges whose
index occurs in the contract index list. -/
def cfcontractMask (cf : Config) : List Bool := ctrmask cf.prog cf.contract

/-- **The contract of a configuration**: a transversal of the edges of
`cfmap cf` that the contract erases. -/
noncomputable def cfcontract (cf : Config) : List (cfmap cf).Dart :=
  listMask (cfcontractMask cf) (ctrenum cf.prog)

/-- The contract of a configuration has one dart per selected kernel edge. -/
theorem length_cfcontract (cf : Config) :
    (cfcontract cf).length = (cfcontractMask cf).count true := by
  have h : (cfcontractMask cf).length = (ctrenum cf.prog).length := by
    rw [cfcontractMask, length_ctrmask, length_ctrenum]
  exact length_listMask h

/-- **A contract never meets the ring.**  The contract of a configuration is
selected from the kernel edge transversal, and `uniq_ctrenum` says that the edge
closure of the transversal is disjoint from the closure of the ring; in
particular no contracted dart is a ring dart.  This is the `off_ring` half of
`Hypermap.ValidContract`. -/
theorem notMem_cfring_of_mem_insertE_cfcontract {cf : Config} (hcfg : ConfigProg cf.prog)
    {x : (cfmap cf).Dart} (hx : x ∈ (cfmap cf).map.insertE (cfcontract cf)) :
    x ∉ cfring cf := by
  intro hr
  have hsub : ∀ y ∈ cfcontract cf, y ∈ ctrenum cf.prog := fun y hy =>
    mem_of_mem_listMask (cfcontractMask cf) (ctrenum cf.prog) hy
  have h1 : x ∈ (cpmap cf.prog).map.insertE (ctrenum cf.prog) :=
    insertE_mono (cpmap cf.prog).map hsub hx
  have hrev : x ∈ ((cpmap cf.prog).cpring).reverse := hr
  have h2 : x ∈ (cpmap cf.prog).map.insertE (cpmap cf.prog).cpring :=
    mem_insertE_self _ (List.mem_reverse.mp hrev)
  have hnd := uniq_ctrenum hcfg
  rw [Hypermap.insertE_append] at hnd
  exact (List.nodup_append.mp hnd).2.2 _ h2 _ h1 rfl

/-- **The tree of the contract colourings of a configuration**, computed as the
colouring tree of the contracted program — provided the configuration program is
well formed and its contract is sparse (so that `cfctr` succeeds) and valid. -/
def contractCtree (cf : Config) : Option Ctree :=
  match cfctr cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf) with
  | some cpc =>
      if validCtrm (cfcontractMask cf) cf.prog then some (cpcolor cpc) else none
  | none => none

/-- A valid contract of a configuration is nonempty. -/
theorem one_le_length_cfcontract {cf : Config}
    (h : validCtrm (cfcontractMask cf) cf.prog) : 1 ≤ (cfcontract cf).length := by
  rw [length_cfcontract]
  exact count_pos_of_validCtrm h

/-- A valid contract of a configuration has at most four darts, as
`Hypermap.ValidContract` requires. -/
theorem length_cfcontract_le_four {cf : Config}
    (h : validCtrm (cfcontractMask cf) cf.prog) : (cfcontract cf).length ≤ 4 := by
  rw [length_cfcontract]
  exact count_le_four_of_validCtrm h

/-- If the contract computation succeeds then the contracted map has the same
ring size as the configuration map, and the tree returned is the colouring tree
of the contracted program. -/
theorem exists_cfctr_of_contractCtree {cf : Config} {ct : Ctree}
    (h : contractCtree cf = some ct) :
    ∃ cpc, cfctr cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf)
        = some cpc ∧ cprsize cpc = cprsize cf.prog ∧ ct = cpcolor cpc := by
  rw [contractCtree] at h
  split at h
  · rename_i cpc hcpc
    refine ⟨cpc, hcpc, cprsize_cfctr_replicate ?_ hcpc, ?_⟩
    · rw [cfcontractMask, length_ctrmask]
    · split at h
      · exact (Option.some_injective _ h).symm
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- If the contract computation succeeds then the configuration program is a
configuration program: the check on the 633 configurations is a proof. -/
theorem ConfigProg.of_contractCtree {cf : Config} {ct : Ctree}
    (h : contractCtree cf = some ct) : ConfigProg cf.prog := by
  rw [contractCtree] at h
  split at h
  · rename_i cpc hcpc
    exact ConfigProg.of_cfctr hcpc
  · exact absurd h (by simp)

/-! ### The triad of a four-edge contract

When the contract has four edges, `validCtrm` checks `cptriad`, which looks for
a kernel face adjacent to at least three of the faces the contract meets and
missing at least one of them.  The two list lemmas below turn the bit counts
`cptriad` computes into darts of the configuration map. -/

/-- Selecting from a list gives a sublist. -/
private theorem listMask_sublist {α : Type*} : ∀ (m : List Bool) (l : List α),
    (listMask m l).Sublist l := by
  intro m
  induction m with
  | nil => intro l; rw [listMask_nil_mask]; exact List.nil_sublist l
  | cons b m ih =>
    intro l
    cases l with
    | nil => rw [listMask_nil_list]
    | cons x l =>
      cases b
      · rw [listMask_false]; exact (ih l).cons x
      · rw [listMask_true]; exact (ih l).cons_cons x

/-- **The darts two masks select in common.**  If the second mask has `n` true
bits among the positions the first mask selects, then `n` distinct darts of the
list are selected by both masks. -/
private theorem exists_listMask_both {α : Type*} : ∀ (m m' : List Bool) (l : List α),
    m.length = l.length → m'.length = l.length → l.Nodup →
    ∃ s : List α, s.Nodup ∧ (listMask m m').count true ≤ s.length
      ∧ ∀ z ∈ s, z ∈ listMask m l ∧ z ∈ listMask m' l := by
  intro m
  induction m with
  | nil => intro m' l _ _ _; exact ⟨[], List.nodup_nil, by simp [listMask_nil_mask], by simp⟩
  | cons b m ih =>
    intro m' l hlen hlen' hnd
    cases l with
    | nil => simp at hlen
    | cons x l =>
      cases m' with
      | nil => simp at hlen'
      | cons b' m' =>
        have hlen1 : m.length = l.length := by simpa using hlen
        have hlen2 : m'.length = l.length := by simpa using hlen'
        have hnd1 : l.Nodup := (List.nodup_cons.mp hnd).2
        have hxl : x ∉ l := (List.nodup_cons.mp hnd).1
        obtain ⟨s, hs1, hs2, hs3⟩ := ih m' l hlen1 hlen2 hnd1
        cases b
        · refine ⟨s, hs1, ?_, ?_⟩
          · rw [listMask_false]; exact hs2
          · intro z hz
            refine ⟨by rw [listMask_false]; exact (hs3 z hz).1, ?_⟩
            cases b'
            · rw [listMask_false]; exact (hs3 z hz).2
            · rw [listMask_true]; exact List.Mem.tail _ (hs3 z hz).2
        · cases b'
          · refine ⟨s, hs1, ?_, ?_⟩
            · rw [listMask_true]; simpa using hs2
            · intro z hz
              exact ⟨by rw [listMask_true]; exact List.Mem.tail _ (hs3 z hz).1,
                by rw [listMask_false]; exact (hs3 z hz).2⟩
          · refine ⟨x :: s, ?_, ?_, ?_⟩
            · refine List.nodup_cons.mpr ⟨fun hc => hxl ?_, hs1⟩
              exact (listMask_sublist m l).subset ((hs3 x hc).1)
            · have hcnt : (listMask (true :: m) (true :: m')).count true
                  = (listMask m m').count true + 1 := by
                rw [listMask_true, List.count_cons]
                simp
              rw [hcnt, List.length_cons]
              omega
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact ⟨by rw [listMask_true]; exact List.Mem.head _,
                  by rw [listMask_true]; exact List.Mem.head _⟩
              · exact ⟨by rw [listMask_true]; exact List.Mem.tail _ (hs3 z hz).1,
                  by rw [listMask_true]; exact List.Mem.tail _ (hs3 z hz).2⟩

/-- **A dart the first mask selects and the second misses.**  If the second mask
has a false bit among the positions the first mask selects, some dart of the
list is selected by the first mask and not by the second. -/
private theorem exists_listMask_not {α : Type*} : ∀ (m m' : List Bool) (l : List α),
    m.length = l.length → m'.length = l.length → l.Nodup → false ∈ listMask m m' →
    ∃ z ∈ listMask m l, z ∉ listMask m' l := by
  intro m
  induction m with
  | nil => intro m' l _ _ _ hf; rw [listMask_nil_mask] at hf; exact absurd hf (by simp)
  | cons b m ih =>
    intro m' l hlen hlen' hnd hf
    cases l with
    | nil => simp at hlen
    | cons x l =>
      cases m' with
      | nil => simp at hlen'
      | cons b' m' =>
        have hlen1 : m.length = l.length := by simpa using hlen
        have hlen2 : m'.length = l.length := by simpa using hlen'
        have hnd1 : l.Nodup := (List.nodup_cons.mp hnd).2
        have hxl : x ∉ l := (List.nodup_cons.mp hnd).1
        cases b
        · rw [listMask_false] at hf
          obtain ⟨z, hz1, hz2⟩ := ih m' l hlen1 hlen2 hnd1 hf
          refine ⟨z, by rw [listMask_false]; exact hz1, ?_⟩
          cases b'
          · rw [listMask_false]; exact hz2
          · rw [listMask_true]
            intro hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact hxl ((listMask_sublist m l).subset hz1)
            · exact hz2 hc
        · rw [listMask_true] at hf
          rcases List.mem_cons.mp hf with hb | hf
          · obtain rfl : b' = false := hb.symm
            refine ⟨x, by rw [listMask_true]; exact List.Mem.head _, ?_⟩
            rw [listMask_false]
            exact fun hc => hxl ((listMask_sublist m' l).subset hc)
          · obtain ⟨z, hz1, hz2⟩ := ih m' l hlen1 hlen2 hnd1 hf
            refine ⟨z, by rw [listMask_true]; exact List.Mem.tail _ hz1, ?_⟩
            cases b'
            · rw [listMask_false]; exact hz2
            · rw [listMask_true]
              intro hc
              rcases List.mem_cons.mp hc with rfl | hc
              · exact hxl ((listMask_sublist m l).subset hz1)
              · exact hz2 hc

/-- The mask selecting the `i`-th kernel face is proper. -/
private theorem proper_cfmask1 (cp : CProg) (i : ℕ) : (cfmask1 cp i).Proper cp := by
  refine ⟨by simp [cfmask1], by simp [cfmask1]⟩

/-- Two darts of a face-simple list on a common face are equal. -/
private theorem eq_of_simple_cface {D : Type*} [Finite D] {G : Hypermap D} :
    ∀ {q : List D}, G.Simple q → ∀ {a b : D}, a ∈ q → b ∈ q → G.CFace a b → a = b := by
  intro q
  induction q with
  | nil => intro _ a b ha _ _; exact absurd ha (by simp)
  | cons c q ih =>
    intro hq a b ha hb hab
    simp only [Hypermap.Simple, List.pairwise_cons] at hq
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd hab (hq.1 b hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd hab.symm (hq.1 a ha')
      · exact ih hq.2 ha' hb' hab

/-- **A kernel face that `cptriad` accepts is a triad for the contract.**  The
band mask meets at least three of the faces adjacent to the kernel face and
misses at least one, which is exactly what `Hypermap.Triad` asks for. -/
private theorem triad_of_cptriad {cp : CProg} (hcfg : ConfigProg cp) {cm : List Bool}
    (hcm : cm.length = ctrmsize cp) :
    ∀ i : ℕ, i ≤ cpksize cp → cptriad (ctrband cp cm) cp i = true →
    ∃ x, (cpmap cp).map.Kernel (cpmap cp).cpring x
      ∧ (cpmap cp).map.Triad ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) x := by
  have hplain : (cpmap cp).map.Plain := cpmap_plain hcfg.cubicProg
  have hsimple : (cpmap cp).map.Simple ((cpmap cp).cpring ++ cpker cp) := cpmap_simple hcfg
  have hnd : ((cpmap cp).cpring ++ cpker cp).Nodup := by
    refine List.Pairwise.imp ?_ hsimple
    intro a b hab heq
    exact hab (by rw [heq])
  have hlenr : (cpmap cp).cpring.length = cprsize cp := size_ring_cpmap cp
  have hlenk : (cpker cp).length = cpksize cp := size_cpker hcfg
  have hccmP : (ctrband cp cm).Proper cp := properCfMask_ctrband hcfg hcm
  intro i
  induction i with
  | zero => intro _ h; exact absurd h (by simp [cptriad])
  | succ i ih =>
    intro hi h
    simp only [cptriad] at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h1
    · have hi' : i < cpksize cp := Nat.lt_of_succ_le hi
      have hix : i < (cpker cp).length := by rw [hlenk]; exact hi'
      have hmtP : (cpadj (cfmask1 cp i) cp).Proper cp :=
        cpadj_proper cp (cfmask1 cp i) (proper_cfmask1 cp i)
      obtain ⟨x, hxdef⟩ : ∃ x, x = (cpker cp)[i]'hix := ⟨_, rfl⟩
      have hxmem : x ∈ cpker cp := by rw [hxdef]; exact List.getElem_mem _
      have hx1 : cpmask (cfmask1 cp i) cp = [x] := by
        rw [hxdef]; exact cpmask1 cp i hcfg hi'
      have hadjx : ∀ u : (cpmap cp).Dart,
          (cpmap cp).map.Fband (cpmask (cpadj (cfmask1 cp i) cp) cp) u
            ↔ (cpmap cp).map.Adj u x := by
        intro u
        rw [cpmask_adj hcfg (proper_cfmask1 cp i) u, hx1]
        simp
      -- the masks as single masks of the perimeter and kernel transversal
      have hlenM : ((ctrband cp cm).ring ++ (ctrband cp cm).kernel).length
          = ((cpmap cp).cpring ++ cpker cp).length := by
        rw [List.length_append, List.length_append, hccmP.1, hccmP.2, hlenr, hlenk]
      have hlenM' : ((cpadj (cfmask1 cp i) cp).ring ++ (cpadj (cfmask1 cp i) cp).kernel).length
          = ((cpmap cp).cpring ++ cpker cp).length := by
        rw [List.length_append, List.length_append, hmtP.1, hmtP.2, hlenr, hlenk]
      have hMq : cpmask (ctrband cp cm) cp
          = listMask ((ctrband cp cm).ring ++ (ctrband cp cm).kernel)
              ((cpmap cp).cpring ++ cpker cp) :=
        (listMask_append _ _ (by rw [hccmP.1, hlenr]) _ _).symm
      have hM'q : cpmask (cpadj (cfmask1 cp i) cp) cp
          = listMask ((cpadj (cfmask1 cp i) cp).ring ++ (cpadj (cfmask1 cp i) cp).kernel)
              ((cpmap cp).cpring ++ cpker cp) :=
        (listMask_append _ _ (by rw [hmtP.1, hlenr]) _ _).symm
      have hmct : listMask (ctrband cp cm).ring (cpadj (cfmask1 cp i) cp).ring
            ++ listMask (ctrband cp cm).kernel (cpadj (cfmask1 cp i) cp).kernel
          = listMask ((ctrband cp cm).ring ++ (ctrband cp cm).kernel)
              ((cpadj (cfmask1 cp i) cp).ring ++ (cpadj (cfmask1 cp i) cp).kernel) :=
        (listMask_append _ _ (by rw [hccmP.1, hmtP.1]) _ _).symm
      -- membership in a masked sublist is being in its band
      have hband : ∀ mm : List Bool, ∀ z ∈ (cpmap cp).cpring ++ cpker cp,
          ((cpmap cp).map.Fband (listMask mm ((cpmap cp).cpring ++ cpker cp)) z
            ↔ z ∈ listMask mm ((cpmap cp).cpring ++ cpker cp)) := by
        intro mm z hz
        refine ⟨?_, fun hz' => ⟨z, hz', Equiv.Perm.SameCycle.refl _ _⟩⟩
        rintro ⟨w, hw, hzw⟩
        have hwq := (listMask_sublist mm _).subset hw
        rw [eq_of_simple_cface hsimple hz hwq hzw]
        exact hw
      obtain ⟨hfalse, hcount⟩ := Bool.and_eq_true_iff.mp h1
      have hfalse' : false ∈ listMask ((ctrband cp cm).ring ++ (ctrband cp cm).kernel)
          ((cpadj (cfmask1 cp i) cp).ring ++ (cpadj (cfmask1 cp i) cp).kernel) := by
        rw [← hmct]; simpa using hfalse
      have hcount' : 3 ≤ (listMask ((ctrband cp cm).ring ++ (ctrband cp cm).kernel)
          ((cpadj (cfmask1 cp i) cp).ring
            ++ (cpadj (cfmask1 cp i) cp).kernel)).count true := by
        rw [← hmct]; simpa using hcount
      -- the face the contract misses
      obtain ⟨z, hz1, hz2⟩ := exists_listMask_not _ _ _ hlenM hlenM' hnd hfalse'
      have hzq : z ∈ (cpmap cp).cpring ++ cpker cp := (listMask_sublist _ _).subset hz1
      have hznadj : ¬ (cpmap cp).map.Adj z x := by
        intro hc
        refine hz2 ((hband _ z hzq).mp ?_)
        rw [← hM'q]
        exact (hadjx z).mpr hc
      have hzband : (cpmap cp).map.Fband
          ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) z := by
        rw [ctrband_correct hcfg hcm z, hMq]
        exact ⟨z, hz1, Equiv.Perm.SameCycle.refl _ _⟩
      obtain ⟨y₀, hy₀1, hy₀2⟩ := hzband
      have hnadj : ¬ (cpmap cp).map.Adj x y₀ := by
        intro hc
        exact hznadj (((cpmap cp).map.adj_congr_left hy₀2 x).mpr (hplain.adj_symm hc))
      -- the three faces the contract meets
      obtain ⟨s, hs1, hs2, hs3⟩ := exists_listMask_both _ _ _ hlenM hlenM' hnd
      have hs2' : 3 ≤ s.length := le_trans hcount' hs2
      have hzqs : ∀ w ∈ s, w ∈ (cpmap cp).cpring ++ cpker cp :=
        fun w hw => (listMask_sublist _ _).subset (hs3 w hw).1
      have hmk : ∀ w ∈ s, ∃ y, (cpmap cp).map.CFace x y
          ∧ (cpmap cp).map.Fband ((cpmap cp).map.insertE (listMask cm (ctrenum cp)))
              ((cpmap cp).map.edge y)
          ∧ (cpmap cp).map.CFace w ((cpmap cp).map.edge y) := by
        intro w hw
        obtain ⟨hwM, hwM'⟩ := hs3 w hw
        have hadjw : (cpmap cp).map.Adj w x := by
          refine (hadjx w).mp ?_
          rw [hM'q]
          exact ⟨w, hwM', Equiv.Perm.SameCycle.refl _ _⟩
        obtain ⟨v, hv1, hv2⟩ := hadjw
        have hwband : (cpmap cp).map.Fband
            ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) w := by
          rw [ctrband_correct hcfg hcm w, hMq]
          exact ⟨w, hwM, Equiv.Perm.SameCycle.refl _ _⟩
        obtain ⟨u, hu1, hu2⟩ := hwband
        refine ⟨(cpmap cp).map.edge v, hv2.symm, ?_, ?_⟩
        · rw [hplain.edge_edge]
          exact ⟨u, hu1, hv1.symm.trans hu2⟩
        · rw [hplain.edge_edge]
          exact hv1
      obtain ⟨z₁, z₂, z₃, tl, hst⟩ : ∃ z₁ z₂ z₃ tl, s = z₁ :: z₂ :: z₃ :: tl := by
        match s, hs2' with
        | [], hh => simp at hh
        | [_], hh => simp at hh
        | [_, _], hh => simp at hh
        | a :: b :: c :: tl, _ => exact ⟨a, b, c, tl, rfl⟩
      subst hst
      obtain ⟨h1', hs1'⟩ := List.nodup_cons.mp hs1
      obtain ⟨h2', -⟩ := List.nodup_cons.mp hs1'
      have hz12 : z₁ ≠ z₂ := fun hc => h1' (by rw [hc]; exact List.Mem.head _)
      have hz13 : z₁ ≠ z₃ := fun hc => h1' (by rw [hc]; exact List.Mem.tail _ (List.Mem.head _))
      have hz23 : z₂ ≠ z₃ := fun hc => h2' (by rw [hc]; exact List.Mem.head _)
      obtain ⟨y₁, hy₁a, hy₁b, hy₁c⟩ := hmk z₁ (by simp)
      obtain ⟨y₂, hy₂a, hy₂b, hy₂c⟩ := hmk z₂ (by simp)
      obtain ⟨y₃, hy₃a, hy₃b, hy₃c⟩ := hmk z₃ (by simp)
      have hyinj : ∀ a b ya yb : (cpmap cp).Dart,
          a ∈ (z₁ :: z₂ :: z₃ :: tl) → b ∈ (z₁ :: z₂ :: z₃ :: tl) →
          (cpmap cp).map.CFace a ((cpmap cp).map.edge ya) →
          (cpmap cp).map.CFace b ((cpmap cp).map.edge yb) → ya = yb → a = b := by
        intro a b ya yb ha hb hca hcb hy
        rw [hy] at hca
        exact eq_of_simple_cface hsimple (hzqs a ha) (hzqs b hb) (hca.trans hcb.symm)
      have hne12 : y₁ ≠ y₂ :=
        fun hc => hz12 (hyinj z₁ z₂ y₁ y₂ (by simp) (by simp) hy₁c hy₂c hc)
      have hne13 : y₁ ≠ y₃ :=
        fun hc => hz13 (hyinj z₁ z₃ y₁ y₃ (by simp) (by simp) hy₁c hy₃c hc)
      have hne23 : y₂ ≠ y₃ :=
        fun hc => hz23 (hyinj z₂ z₃ y₂ y₃ (by simp) (by simp) hy₂c hy₃c hc)
      refine ⟨x, ?_, ⟨?_, ⟨y₀, hy₀1, hnadj⟩⟩⟩
      · rintro ⟨w, hw, hxw⟩
        have heq : x = w := eq_of_simple_cface hsimple (List.mem_append_right _ hxmem)
          (List.mem_append_left _ hw) hxw
        exact (List.nodup_append.mp hnd).2.2 w hw x hxmem heq.symm
      · have hsub : ({y₁, y₂, y₃} : Set (cpmap cp).Dart)
            ⊆ (cpmap cp).map.triadSet
                ((cpmap cp).map.insertE (listMask cm (ctrenum cp))) x := by
          rintro y hy
          rcases hy with rfl | rfl | rfl
          · exact ⟨hy₁a, hy₁b⟩
          · exact ⟨hy₂a, hy₂b⟩
          · exact ⟨hy₃a, hy₃b⟩
        have hcard : ({y₁, y₂, y₃} : Set (cpmap cp).Dart).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by simp [hne12, hne13]),
            Set.ncard_insert_of_notMem (by simp [hne23]), Set.ncard_singleton]
        rw [← hcard]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
    · exact ih (Nat.le_of_succ_le hi) h1

/-! ### The contract of a configuration is valid -/

/-- Composing a colouring with a colour permutation gives a colouring. -/
private theorem coloring_map_edgePerm {D : Type*} [Finite D] {G : Hypermap D}
    {k : D → Color} (g : EdgePerm) (h : G.Coloring k) : G.Coloring (fun x => g (k x)) :=
  ⟨fun x hc => h.edge x (g.apply_injective hc), fun x => by rw [h.face]⟩

/-- Selecting with an all-`true` mask keeps the whole list. -/
private theorem listMask_eq_self {α : Type*} : ∀ (m : List Bool) (l : List α),
    m.length = l.length → (∀ b ∈ m, b = true) → listMask m l = l := by
  intro m
  induction m with
  | nil =>
    intro l hlen _
    cases l with
    | nil => rfl
    | cons x l => simp at hlen
  | cons b m ih =>
    intro l hlen hall
    cases l with
    | nil => simp at hlen
    | cons x l =>
      obtain rfl : b = true := hall b List.mem_cons_self
      rw [listMask_true, ih l (by simpa using hlen) (fun c hc => hall c (List.Mem.tail _ hc))]

/-- **The contract of a configuration is valid, and its contract colourings are
in the tree.**  This is the last ingredient of the reducibility check: when
`contractCtree` succeeds, the contract it ran on is a valid contract of the
configuration map, and every contract ring trace of that contract occurs, in
canonical form, in the tree it returns. -/
theorem contract_ctreeP {cf : Config} {ct : Ctree} (h : contractCtree cf = some ct) :
    (cfmap cf).map.ValidContract (cfring cf) (cfcontract cf)
      ∧ ∀ et : List Color,
          (cfmap cf).map.CcRingTrace (cfcontract cf) (cfring cf).reverse et →
          Ctree.mem ct (evenize et.tail) = true := by
  have hcfg : ConfigProg cf.prog := ConfigProg.of_contractCtree h
  obtain ⟨cpc, hcpc, -, hct⟩ := exists_cfctr_of_contractCtree h
  have hvalid : validCtrm (cfcontractMask cf) cf.prog = true := by
    by_contra hc
    simp only [contractCtree, hcpc] at h
    rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  have hmr0 : (List.replicate (cprsize cf.prog) false).length = cprsize cf.prog := by simp
  have hcm : (cfcontractMask cf).length = ctrmsize cf.prog := by
    rw [cfcontractMask, length_ctrmask]
  have hnilmask : listMask (List.replicate (cprsize cf.prog) false) (cpmap cf.prog).cpring
      = [] := listMask_eq_nil _ _ fun b hb => List.eq_of_mem_replicate hb
  have hctr : ctrList cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf)
      = (cfmap cf).map.insertE (cfcontract cf) := by
    rw [ctrList, hnilmask, List.map_nil, List.nil_append]
    rfl
  have hsp := sparse_cfctr hmr0 hcm hcpc
  rw [hctr] at hsp
  have hsparse : (cfmap cf).map.Sparse ((cfmap cf).map.insertE (cfcontract cf)) :=
    (Hypermap.sparse_cons.mp hsp).2
  have hrev : (cfring cf).reverse = (cpmap cf.prog).cpring := by
    rw [cfring, List.reverse_reverse]
    rfl
  have htriad : (cfcontract cf).length = 4 →
      ∃ x, (cfmap cf).map.Kernel (cfring cf) x
        ∧ (cfmap cf).map.Triad ((cfmap cf).map.insertE (cfcontract cf)) x := by
    intro hlen4
    rw [length_cfcontract] at hlen4
    have hv := hvalid
    rw [validCtrm, ite_eq_left hlen4] at hv
    obtain ⟨x, hx1, hx2⟩ := triad_of_cptriad hcfg hcm (cpksize cf.prog) le_rfl hv
    refine ⟨x, ?_, hx2⟩
    rintro ⟨w, hw, hxw⟩
    rw [cfring, List.mem_reverse] at hw
    exact hx1 ⟨w, hw, hxw⟩
  refine ⟨⟨fun x hx => notMem_cfring_of_mem_insertE_cfcontract hcfg hx, hsparse,
    one_le_length_cfcontract hvalid, length_cfcontract_le_four hvalid, htriad⟩, ?_⟩
  intro et het
  obtain ⟨k, hk, hetdef⟩ := het
  rw [hrev] at hetdef
  rw [hct]
  have hk' : (cpmap cf.prog).map.CcColoring
      (listMask (List.replicate (cprsize cf.prog) false) (cpmap cf.prog).cpring
        ++ listMask (cfcontractMask cf) (ctrenum cf.prog)) k := by
    rw [hnilmask, List.nil_append]
    exact hk
  obtain ⟨k', hk'col, hk'ring⟩ := cfctr_correct hmr0 hcm hcpc k hk'
  have hmasktrue : listMask ((List.replicate (cprsize cf.prog) false).map not)
      (cpmap cf.prog).cpring = (cpmap cf.prog).cpring := by
    refine listMask_eq_self _ _ ?_ ?_
    · rw [List.length_map, List.length_replicate, size_ring_cpmap]
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      rw [List.eq_of_mem_replicate hc]
      rfl
  rw [hmasktrue] at hk'ring
  have hetne : et ≠ [] := by
    have h1 : et.length = (cpmap cf.prog).cpring.length := by
      rw [hetdef, length_trace]
      exact List.length_map ..
    intro hc
    rw [hc, List.length_nil] at h1
    exact absurd h1.symm (Nat.ne_of_gt Hypermap.length_cpring_pos)
  obtain ⟨e₀, et', hete⟩ := List.exists_cons_of_ne_nil hetne
  have he₀ : e₀ = et'.sum := by
    have h1 : et.sum = 0 := by rw [hetdef]; exact sum_trace _
    rw [hete, List.sum_cons] at h1
    exact Color.add_eq_zero_iff.mp h1
  refine (ctree_mem_cpcolor cpc (evenize et.tail)).mpr ⟨evenTrace_evenize _, ?_⟩
  refine ⟨fun w => (evenPerm et.tail) (k' w), coloring_map_edgePerm _ hk'col, ?_⟩
  have hmapcomp : (cpmap cpc).cpring.map (fun w => (evenPerm et.tail) (k' w))
      = ((cpmap cpc).cpring.map k').map (evenPerm et.tail) := by
    rw [List.map_map]
    rfl
  have htr : trace ((cpmap cpc).cpring.map (fun w => (evenPerm et.tail) (k' w)))
      = et.map (evenPerm et.tail) := by
    rw [hmapcomp, trace_map, hk'ring]
    exact congrArg (fun l => l.map (evenPerm et.tail)) hetdef.symm
  rw [htr, hete]
  simp only [List.tail_cons, evenize, List.map_cons]
  rw [map_sum, ← he₀]

end FourColor

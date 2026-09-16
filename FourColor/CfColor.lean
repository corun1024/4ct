import FourColor.CfMap
import FourColor.Ctree

/-!
# Colouring a configuration map

The set of ring traces of the colourings of a configuration map is computed
directly from the construction program, as a `Ctree`.  The computation is a
fold of the program: each construction step turns a function producing the
trees of a map into a function producing the trees of the extended map, by
enumerating the ways a colouring of the extension restricts to the smaller map.

Because only the *even normalised tail* of a trace is stored, the leaf of the
recursion, `cpbranch`, does the rotation and the `c2`/`c3` swap in a single
pass; `cpbranch_spec` identifies it with `Ctree.ofTrace ∘ evenNormTail ∘ tail`.

## Main definitions

* `cpbranch` — the optimised production of a single tree branch from a trace.
* `cpcolor1` — the step functional: one construction step of the fold.
* `cpcolor0`, `cpcolor` — the colouring tree of a construction program.
* `cpexpand` — rewriting `Y` and `H` steps as sequences of `U`, `K` and
  rotation steps, which is what makes the fold correct by a single induction.
* `CpExtcol` — the invariant the fold maintains, and `CpTrace0`, `cpHeight`,
  the trace and height it refers to; `CpExtcolT` is the same invariant stated
  for abstract maps, in which form it transports along `CpExtcolT.congr`.
* `BaseMap` — the single-edge map a program starts from, up to rotation, and
  `kU0`, `kY0`, the colourings of its `U` and `Y` extensions that justify the
  extra symmetry reductions of `cpcolor0`.

## Main results

* `cpbranch_spec` — `cpbranch et = Ctree.ofTrace (evenNormTail et.tail)`.
* `Hypermap.Coloring.zero_notMem_trace_cpring`, `Coloring.properCpring`,
  `Coloring.properTrace_tail_trace_cpring` — a ring trace of a colouring never
  contains `c0`, so a colourable pointed map has a nontrivial ring and the tail
  of its ring trace is a proper trace.
* `cpbranch_correct`, `cpcolor1R_correct`, `cpcolor1R'_correct` — the leaf and
  the two rotation steps of the fold satisfy `CpExtcol`.
* `cpcolor1_congr`, `cpcolor1Y_expand`, `cpcolor1H_expand` and
  `foldr_cpcolor1_cpexpand` — expanding the composite steps leaves the computed
  tree unchanged on `c0`-free traces.
* `cpcolor1U_correct`, `cpcolor1K_correct`, `cpcolor1A_correct`,
  `cpcolor1Y_correct`, `cpcolor1H_correct` — the remaining steps of the fold
  satisfy `CpExtcol`; the last two are obtained by expanding the step.
* `cpcolor1_correct` — **the fold is correct**: for every program and every
  colouring of the base map it computes the tree of the canonical ring traces of
  the colourings extending it.
* `cpcolor0_correct` — the same for `cpcolor0`, including its extra symmetry
  reductions at the first `U` or `Y` step.
* `cpcolor_proper` — `cpcolor cp` is a proper tree of height `cprsize cp - 1`.
* `ctree_mem_cpcolor` — **the specification of `cpcolor`**: `cpcolor cp` holds
  exactly the even traces whose completion is a ring trace of `cpmap cp`.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/cfcolor.v` of the Coq development.
-/

namespace FourColor

open Color EdgePerm

/-! ### The trace branch

`cpbranch et` is the one-branch tree holding the canonical form of the tail of
`et`.  It is written as a single pass so that the colouring computation never
builds the intermediate normalised list. -/

/-- The permutation normalising the parity of a tail: the identity on even
tails, and the transposition of `c2` and `c3` on odd ones.  This is `evenPerm`
read off the *already normalised* tail. -/
def evenTailPerm (u : List Color) : EdgePerm := if evenTail u then 1 else e132

theorem evenPerm_eq_evenTailPerm (et : List Color) :
    evenPerm et = evenTailPerm (normTail et) := rfl

theorem evenNormTail_eq (et : List Color) :
    evenNormTail et = (normTail et).map (evenTailPerm (normTail et)) := rfl

@[simp] theorem evenTailPerm_nil : evenTailPerm [] = 1 := rfl

@[simp] theorem evenTailPerm_cons_c0 (u : List Color) :
    evenTailPerm (c0 :: u) = evenTailPerm u := rfl

@[simp] theorem evenTailPerm_cons_c1 (u : List Color) :
    evenTailPerm (c1 :: u) = evenTailPerm u := rfl

@[simp] theorem evenTailPerm_cons_c2 (u : List Color) : evenTailPerm (c2 :: u) = 1 := rfl

@[simp] theorem evenTailPerm_cons_c3 (u : List Color) : evenTailPerm (c3 :: u) = e132 := rfl

theorem evenTailPerm_eq_one_or (u : List Color) : evenTailPerm u = 1 ∨ evenTailPerm u = e132 := by
  unfold evenTailPerm; split <;> simp

@[simp] theorem evenTailPerm_apply_c0 (u : List Color) : (evenTailPerm u) c0 = c0 := by
  rcases evenTailPerm_eq_one_or u with h | h <;> rw [h] <;> rfl

@[simp] theorem evenTailPerm_apply_c1 (u : List Color) : (evenTailPerm u) c1 = c1 := by
  rcases evenTailPerm_eq_one_or u with h | h <;> rw [h] <;> rfl

/-- The body of a trace branch: the tree containing exactly `et.map g`,
renormalised for parity on the fly. -/
def cfcbr1 (g : EdgePerm) : List Color → Ctree
  | [] => Ctree.simpleLeaf
  | e :: et =>
    match g e with
    | .c0 => .empty
    | .c1 => Ctree.consE c1 (cfcbr1 g et)
    | .c2 => Ctree.consE c2 (Ctree.ofTrace (et.map g))
    | .c3 => Ctree.consE c2 (Ctree.ofTrace (et.map (e132 * g)))

@[simp] theorem cfcbr1_nil (g : EdgePerm) : cfcbr1 g [] = Ctree.simpleLeaf := rfl

theorem cfcbr1_cons (g : EdgePerm) (e : Color) (et : List Color) :
    cfcbr1 g (e :: et) =
      match g e with
      | .c0 => .empty
      | .c1 => Ctree.consE c1 (cfcbr1 g et)
      | .c2 => Ctree.consE c2 (Ctree.ofTrace (et.map g))
      | .c3 => Ctree.consE c2 (Ctree.ofTrace (et.map (e132 * g))) := rfl

/-- The tree of the canonical form of the tail of a trace. -/
def cpbranch : List Color → Ctree
  | _ :: e :: et => if e = 0 then .empty else cfcbr1 (rotTo e) et
  | _ => .empty

theorem cfcbr1_eq (g : EdgePerm) : ∀ et : List Color,
    cfcbr1 g et = Ctree.ofTrace ((et.map g).map (evenTailPerm (et.map g))) := by
  intro et
  induction et with
  | nil => rfl
  | cons e et ih =>
    have hm : (e :: et).map g = g e :: et.map g := rfl
    rw [cfcbr1_cons, hm, List.map_cons, Ctree.ofTrace_cons]
    cases hge : g e with
    | c0 => rw [evenTailPerm_cons_c0, evenTailPerm_apply_c0]; rfl
    | c1 => rw [evenTailPerm_cons_c1, evenTailPerm_apply_c1, ih]
    | c2 => rw [evenTailPerm_cons_c2, map_one_edgePerm]; rfl
    | c3 => rw [evenTailPerm_cons_c3, map_map_edgePerm]; rfl

/-- `cpbranch` builds exactly the branch of the canonical form of the tail. -/
theorem cpbranch_spec (et : List Color) :
    cpbranch et = Ctree.ofTrace (evenNormTail et.tail) := by
  match et with
  | [] => rfl
  | [_] => rfl
  | _ :: e :: et =>
    by_cases he : e = 0
    · subst he
      rw [cpbranch, ite_eq_left rfl]
      rfl
    · rw [cpbranch, ite_eq_right he, cfcbr1_eq, evenNormTail_eq]
      simp only [List.tail_cons, normTail, ite_eq_right he]

/-! ### The colouring functional

`cpcolor1 s f` turns a function computing the trees of the colourings of a
pointed map `G` into one computing the trees of the colourings of the map `G`
extended by the step `s`.  Each case enumerates the ways the ring trace of the
extended map restricts to a ring trace of `G`; the enumeration does not depend
on `G`, which is what makes the whole computation a fold of the program. -/

/-- One construction step of the colouring fold. -/
def cpcolor1 (s : CpStep) (f : List Color → Ctree) (et : List Color) : Ctree :=
  match s, et with
  | .R n, _ => f (et.rotate n)
  | .R', _ => if et.length ≤ 1 then .empty else f (et.rotate (et.length - 1))
  | .U, _ =>
      Ctree.union (f (c1 :: c1 :: et))
        (Ctree.union (f (c2 :: c2 :: et)) (f (c3 :: c3 :: et)))
  | .Y, e₁ :: et' =>
      Ctree.union (f (e231 e₁ :: e312 e₁ :: et')) (f (e312 e₁ :: e231 e₁ :: et'))
  | .K, e₁ :: e₂ :: et' => if e₁ = e₂ then .empty else f ((e₁ + e₂) :: et')
  | .H, e₁ :: e₂ :: et' =>
      if e₁ = e₂ then
        Ctree.union (f (e231 e₁ :: e231 e₁ :: et')) (f (e312 e₁ :: e312 e₁ :: et'))
      else f (e₂ :: e₁ :: et')
  | .A, e₁ :: e₂ :: et' =>
      if e₁ = e₂ then f (match et' with | [] => [e₁, e₂] | _ :: _ => et') else .empty
  | _, _ => .empty

@[simp] theorem cpcolor1_R (n : ℕ) (f : List Color → Ctree) (et : List Color) :
    cpcolor1 (.R n) f et = f (et.rotate n) := rfl

@[simp] theorem cpcolor1_R' (f : List Color → Ctree) (et : List Color) :
    cpcolor1 .R' f et =
      if et.length ≤ 1 then .empty else f (et.rotate (et.length - 1)) := rfl

@[simp] theorem cpcolor1_U (f : List Color → Ctree) (et : List Color) :
    cpcolor1 .U f et =
      Ctree.union (f (c1 :: c1 :: et))
        (Ctree.union (f (c2 :: c2 :: et)) (f (c3 :: c3 :: et))) := rfl

@[simp] theorem cpcolor1_Y_nil (f : List Color → Ctree) : cpcolor1 .Y f [] = .empty := rfl

@[simp] theorem cpcolor1_Y_cons (f : List Color → Ctree) (e₁ : Color) (et : List Color) :
    cpcolor1 .Y f (e₁ :: et) =
      Ctree.union (f (e231 e₁ :: e312 e₁ :: et)) (f (e312 e₁ :: e231 e₁ :: et)) := rfl

@[simp] theorem cpcolor1_K_nil (f : List Color → Ctree) : cpcolor1 .K f [] = .empty := rfl

@[simp] theorem cpcolor1_K_singleton (f : List Color → Ctree) (e₁ : Color) :
    cpcolor1 .K f [e₁] = .empty := rfl

@[simp] theorem cpcolor1_K_cons (f : List Color → Ctree) (e₁ e₂ : Color) (et : List Color) :
    cpcolor1 .K f (e₁ :: e₂ :: et) = if e₁ = e₂ then .empty else f ((e₁ + e₂) :: et) := rfl

@[simp] theorem cpcolor1_H_nil (f : List Color → Ctree) : cpcolor1 .H f [] = .empty := rfl

@[simp] theorem cpcolor1_H_singleton (f : List Color → Ctree) (e₁ : Color) :
    cpcolor1 .H f [e₁] = .empty := rfl

@[simp] theorem cpcolor1_H_cons (f : List Color → Ctree) (e₁ e₂ : Color) (et : List Color) :
    cpcolor1 .H f (e₁ :: e₂ :: et) =
      if e₁ = e₂ then
        Ctree.union (f (e231 e₁ :: e231 e₁ :: et)) (f (e312 e₁ :: e312 e₁ :: et))
      else f (e₂ :: e₁ :: et) := rfl

@[simp] theorem cpcolor1_A_nil (f : List Color → Ctree) : cpcolor1 .A f [] = .empty := rfl

@[simp] theorem cpcolor1_A_singleton (f : List Color → Ctree) (e₁ : Color) :
    cpcolor1 .A f [e₁] = .empty := rfl

@[simp] theorem cpcolor1_A_cons (f : List Color → Ctree) (e₁ e₂ : Color) (et : List Color) :
    cpcolor1 .A f (e₁ :: e₂ :: et) =
      if e₁ = e₂ then f (match et with | [] => [e₁, e₂] | _ :: _ => et) else .empty := rfl

/-- The colouring tree of a program, with the extra symmetry reductions that
apply to the outermost steps of the construction: the very first ring may be
coloured up to a rotation and a reflection. -/
def cpcolor0 : CProg → Ctree
  | .R _ :: cp => cpcolor0 cp
  | .Y :: cp => List.foldr cpcolor1 cpbranch cp [c1, c2, c3]
  | .U :: cp =>
      Ctree.union (List.foldr cpcolor1 cpbranch cp [c1, c1, c2, c2])
        (List.foldr cpcolor1 cpbranch cp [c1, c1, c1, c1])
  | cp => List.foldr cpcolor1 cpbranch cp [c1, c1]

/-- The tree of the even, partial ring traces of the colourings of `cpmap cp`. -/
def cpcolor (cp : CProg) : Ctree := Ctree.consRot (cpcolor0 cp.reverse)

/-! ### Expanding the composite steps

A `Y` or an `H` step is a `U` step followed by one or two `K` steps, up to
rotations.  Rewriting the program this way leaves the computed tree unchanged,
which is what lets the correctness proof treat only the four basic steps. -/

-- `cpexpand1` and `cpexpand` are defined in `FourColor.CfMap`.

@[simp] theorem cpexpand_nil : cpexpand [] = [] := rfl

@[simp] theorem cpexpand_cons (s : CpStep) (cp : CProg) :
    cpexpand (s :: cp) = cpexpand1 s ++ cpexpand cp := rfl

theorem cpexpand_append (cp₁ cp₂ : CProg) :
    cpexpand (cp₁ ++ cp₂) = cpexpand cp₁ ++ cpexpand cp₂ := by
  induction cp₁ with
  | nil => rfl
  | cons s cp ih => rw [List.cons_append, cpexpand_cons, ih, cpexpand_cons, List.append_assoc]


/-! ### Ring traces of colourings

Consecutive darts of a ring are `node`-linked, and a colouring gives different
colours to the two ends of a `node` link, so the trace of a ring colouring never
contains `c0`.  In particular a colourable pointed map has a nontrivial ring,
and the tail of its ring trace is a proper trace. -/

namespace Hypermap

variable {D : Type*} {G : Hypermap D} {k : D → Color}

/-- A colouring gives different colours to a dart and to its `node` image: the
dart is the face of the `edge` link out of that image. -/
theorem Coloring.ne_node (hk : G.Coloring k) (x : D) : k x ≠ k (G.node x) := by
  have h : G.face (G.edge (G.node x)) = x := by rw [G.face_edge, G.inv_node_node]
  have h2 : k (G.face (G.edge (G.node x))) = k (G.edge (G.node x)) := hk.face _
  rw [h] at h2
  rw [h2]
  exact hk.edge (G.node x)

/-- No entry of the partial trace of a `node` chain of darts vanishes. -/
theorem Coloring.zero_notMem_pairmap (hk : G.Coloring k) : ∀ {x : D} {p : List D},
    List.IsChain (fun u v => u = G.node v) (x :: p) →
      (0 : Color) ∉ pairmap (· + ·) (k x) (p.map k) := by
  intro x p
  induction p generalizing x with
  | nil => intro _; simp
  | cons y p ih =>
    intro hch hmem
    obtain ⟨hxy, htail⟩ := List.isChain_cons_cons.mp hch
    rw [List.map_cons, pairmap_cons] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · refine hk.ne_node y ?_
      rw [← hxy]
      exact (add_eq_zero_iff.mp h.symm).symm
    · exact ih htail h

/-- The trace of a colouring along a cyclic `node` chain never contains `c0`. -/
theorem Coloring.zero_notMem_trace (hk : G.Coloring k) {r : List D}
    (hcyc : IsCyclicChain (fun u v => u = G.node v) r) :
    (0 : Color) ∉ trace (r.map k) := by
  match r with
  | [] =>
    have hnil : trace ((([] : List D)).map k) = [] := rfl
    rw [hnil]
    simp
  | x :: p =>
    obtain ⟨hch, hlast⟩ := hcyc
    have hl : p.getLastD x = G.node x := hlast _ (getLast?_cons_eq_some x p) x rfl
    have hch' : List.IsChain (fun u v => u = G.node v) ((x :: p) ++ [x]) :=
      isChain_append_cons hch hl (List.IsChain.singleton x)
    have hnz := hk.zero_notMem_pairmap (p := p ++ [x]) hch'
    rw [List.map_cons, trace_cons]
    rw [List.map_append] at hnz
    simpa using hnz

/-- The tail of the ring trace of a colouring is a proper trace. -/
theorem Coloring.properTrace_tail_trace (hk : G.Coloring k) {r : List D}
    (hcyc : IsCyclicChain (fun u v => u = G.node v) r) (hlen : 2 ≤ r.length) :
    ProperTrace (trace (r.map k)).tail := by
  have h0 := hk.zero_notMem_trace hcyc
  have hl : 2 ≤ (trace (r.map k)).length := by simpa using hlen
  obtain ⟨a, b, t, hr⟩ : ∃ a b t, trace (r.map k) = a :: b :: t := by
    match hrr : trace (r.map k) with
    | [] => rw [hrr] at hl; simp at hl
    | [_] => rw [hrr] at hl; simp at hl
    | a :: b :: t => exact ⟨a, b, t, rfl⟩
  rw [hr, List.tail_cons]
  intro hb
  simp only [List.headD_cons] at hb
  exact h0 (by rw [hr, ← hb]; simp)

variable [Finite D]

/-- The ring trace of a colouring never contains `c0`. -/
theorem Coloring.zero_notMem_trace_cpring (hk : G.Coloring k) (x₀ : D) :
    (0 : Color) ∉ trace ((G.cpring x₀).map k) :=
  hk.zero_notMem_trace isCyclicChain_cpring

/-- A colourable pointed map has a nontrivial ring: a one-dart ring would give
the degenerate trace `[c0]`. -/
theorem Coloring.properCpring (hk : G.Coloring k) (x₀ : D) : G.ProperCpring x₀ := by
  rw [proper_cpring_iff]
  by_contra hle
  have hpos : 0 < (G.cpring x₀).length := length_cpring_pos
  have h1 : (G.cpring x₀).length = 1 := by omega
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp h1
  refine hk.zero_notMem_trace_cpring x₀ ?_
  rw [hy]
  simp [trace, partialTrace, completeTrace]

/-- The tail of the ring trace of a colouring is a proper trace. -/
theorem Coloring.properTrace_tail_trace_cpring (hk : G.Coloring k) (x₀ : D) :
    ProperTrace (trace ((G.cpring x₀).map k)).tail :=
  hk.properTrace_tail_trace isCyclicChain_cpring
    (by have := proper_cpring_iff.mp (hk.properCpring x₀); omega)

end Hypermap

/-! ### Tails of traces -/

/-- The tail of a trace is the partial trace of the rotated colouring. -/
theorem tail_trace (l : List Color) : (trace l).tail = partialTrace (l.rotate 1) := by
  match l with
  | [] => rfl
  | [c] => simp [trace, partialTrace, completeTrace]
  | c :: d :: t =>
    have h1 : (c :: d :: t).rotate 1 = d :: (t ++ [c]) := by
      rw [List.rotate_cons_succ, List.rotate_zero, List.cons_append]
    rw [trace_cons, List.cons_append, pairmap_cons, List.tail_cons, h1]
    rfl

/-- The canonical form of a proper trace is one shorter than the trace. -/
theorem length_evenNormTail_of_properTrace {u : List Color} (h : ProperTrace u) :
    (evenNormTail u).length = u.length - 1 := by
  match u with
  | [] => exact absurd rfl h
  | b :: t =>
    have hb : ¬ b = 0 := h
    simp [evenNormTail, normTail, ite_eq_right hb]

/-! ### The colouring invariant

`CpExtcol et0 cp1 cp2 f k` is the invariant the colouring fold maintains: `f`
sends the ring trace of a colouring `k` of `cpmap cp2` to a proper tree, which
contains the normalised tail of `et0` exactly when `k` extends to a colouring
of the map built by running `cp1` on top of `cpmap cp2` whose canonical partial
ring trace is that tail. -/

/-- Two less than the ring size of `cpmap cp`: the height of the trees the
colouring fold produces for `cp`. -/
noncomputable def cpHeight (cp : CProg) : ℕ := (cpmap cp).cpring.length - 2

/-- `CpTrace0 et0 cp k0` says that the normalised tail of `et0` is the canonical
partial ring trace of the colouring `k0` of `cpmap cp`. -/
def CpTrace0 (et0 : List Color) (cp : CProg) (k0 : (cpmap cp).Dart → Color) : Prop :=
  normTail et0 = evenPartialTail (((cpmap cp).cpring.map k0).rotate 1)

/-- The invariant of the colouring fold. -/
structure CpExtcol (et0 : List Color) (cp1 cp2 : CProg) (f : List Color → Ctree)
    (k : (cpmap cp2).Dart → Color) : Prop where
  /-- The tree produced has the height predicted by the resulting ring size. -/
  proper : Ctree.Proper (cpHeight (cp1.reverseAux cp2))
    (f (trace ((cpmap cp2).cpring.map k)))
  /-- It contains exactly the canonical tails of the extensions of `k`. -/
  mem : Ctree.mem (f (trace ((cpmap cp2).cpring.map k))) (normTail et0) = true ↔
      ∃ k0 : (cpmap (cp1.reverseAux cp2)).Dart → Color,
        (cpmap (cp1.reverseAux cp2)).map.Coloring k0 ∧
          CpTrace0 et0 (cp1.reverseAux cp2) k0 ∧
          ∀ x, k0 (injcp cp1 cp2 x) = k x

/-- Recolouring by a colour permutation followed by a translation preserves both
being a colouring and the canonical partial ring trace. -/
theorem CpTrace0.perm {et0 : List Color} {cp : CProg} {k0 : (cpmap cp).Dart → Color}
    (hcol : (cpmap cp).map.Coloring k0) (htr : CpTrace0 et0 cp k0) (c : Color) (g : EdgePerm) :
    (cpmap cp).map.Coloring (fun x => c + g (k0 x)) ∧
      CpTrace0 et0 cp (fun x => c + g (k0 x)) := by
  have hinj : Function.Injective (fun d : Color => c + g d) := by
    intro a b hab
    exact g.apply_injective (by simpa using hab)
  refine ⟨hcol.comp (h := fun d : Color => c + g d) hinj, ?_⟩
  have hm : ((cpmap cp).cpring.map fun x => c + g (k0 x))
      = ((cpmap cp).cpring.map k0).map (fun d => c + g d) := by
    rw [List.map_map]; rfl
  rw [CpTrace0, hm, ← List.map_rotate, evenPartialTail_map hinj]
  exact htr

/-- The leaf of the colouring fold: `cpbranch` applied to the ring trace of a
colouring `k` is the branch of the canonical tail of that trace, and the only
extension of `k` to the same map is `k` itself. -/
theorem cpbranch_correct (et0 : List Color) {cp2 : CProg} {k : (cpmap cp2).Dart → Color}
    (hk : (cpmap cp2).map.Coloring k) : CpExtcol et0 [] cp2 cpbranch k := by
  have h0 : (0 : Color) ∉ trace ((cpmap cp2).cpring.map k) :=
    hk.zero_notMem_trace_cpring _
  have htail : ProperTrace (trace ((cpmap cp2).cpring.map k)).tail :=
    hk.properTrace_tail_trace_cpring _
  have hlen : (trace ((cpmap cp2).cpring.map k)).length = (cpmap cp2).cpring.length := by simp
  have hnz : (0 : Color) ∉ evenNormTail (trace ((cpmap cp2).cpring.map k)).tail := by
    simp only [evenNormTail, mem_zero_map, mem_zero_normTail, not_or, not_not]
    exact ⟨htail, fun hc => h0 (List.mem_of_mem_tail hc)⟩
  have hkey : ∀ k0 : (cpmap cp2).Dart → Color, CpTrace0 et0 cp2 k0 ↔
      normTail et0 = evenNormTail (trace ((cpmap cp2).cpring.map k0)).tail := by
    intro k0
    rw [CpTrace0, evenPartialTail, ← tail_trace]
  refine ⟨?_, ?_⟩
  · rw [cpbranch_spec]
    refine Ctree.ofTrace_proper ?_
    rw [length_evenNormTail_of_properTrace htail, List.length_tail, hlen]
    change (cpmap cp2).cpring.length - 1 - 1 = cpHeight cp2
    rw [cpHeight]
    omega
  · rw [cpbranch_spec, Ctree.mem_ofTrace _ hnz]
    constructor
    · intro h
      exact ⟨k, hk, (hkey k).mpr h, fun _ => rfl⟩
    · rintro ⟨k0, -, htr, hkk⟩
      have hk0 : k0 = k := funext hkk
      subst hk0
      exact (hkey k0).mp htr

/-- A rotation step: the ring is rotated and the map is unchanged. -/
theorem cpcolor1R_correct (et0 : List Color) (n : ℕ) {cp1 cp2 : CProg}
    {f : List Color → Ctree} {k : (cpmap cp2).Dart → Color}
    (hf : CpExtcol et0 cp1 (.R n :: cp2) f k) :
    CpExtcol et0 (.R n :: cp1) cp2 (cpcolor1 (.R n) f) k := by
  have hring : (cpmap (CpStep.R n :: cp2)).cpring = (cpmap cp2).cpring.rotate n :=
    Hypermap.cpring_ecpR n
  have htr : trace ((cpmap (CpStep.R n :: cp2)).cpring.map k)
      = (trace ((cpmap cp2).cpring.map k)).rotate n := by
    rw [hring, List.map_rotate, trace_rotate]
  have hstep : cpcolor1 (CpStep.R n) f (trace ((cpmap cp2).cpring.map k))
      = f (trace ((cpmap (CpStep.R n :: cp2)).cpring.map k)) := by
    rw [cpcolor1_R, ← htr]
  refine ⟨?_, ?_⟩
  · rw [hstep]; exact hf.proper
  · rw [hstep]; exact hf.mem

/-- The backwards rotation step. -/
theorem cpcolor1R'_correct (et0 : List Color) {cp1 cp2 : CProg}
    {f : List Color → Ctree} {k : (cpmap cp2).Dart → Color}
    (hk : (cpmap cp2).map.Coloring k) (hf : CpExtcol et0 cp1 (.R' :: cp2) f k) :
    CpExtcol et0 (.R' :: cp1) cp2 (cpcolor1 .R' f) k := by
  have hper : Function.minimalPeriod (cpmap cp2).map.node (cpmap cp2).point
      = (cpmap cp2).cpring.length := Hypermap.length_cpring.symm
  have hring0 : (cpmap (CpStep.R' :: cp2)).cpring
      = (cpmap cp2).cpring.rotate
          (Function.minimalPeriod (cpmap cp2).map.node (cpmap cp2).point - 1) :=
    Hypermap.cpring_ecpR _
  have hring : (cpmap (CpStep.R' :: cp2)).cpring
      = (cpmap cp2).cpring.rotate ((cpmap cp2).cpring.length - 1) := by
    rw [hring0, hper]
  have hlen : (trace ((cpmap cp2).cpring.map k)).length = (cpmap cp2).cpring.length := by simp
  have hprop : 1 < (cpmap cp2).cpring.length :=
    Hypermap.proper_cpring_iff.mp (hk.properCpring _)
  have htr : trace ((cpmap (CpStep.R' :: cp2)).cpring.map k)
      = (trace ((cpmap cp2).cpring.map k)).rotate
          ((trace ((cpmap cp2).cpring.map k)).length - 1) := by
    rw [hring, List.map_rotate, trace_rotate, hlen]
  have hstep : cpcolor1 CpStep.R' f (trace ((cpmap cp2).cpring.map k))
      = f (trace ((cpmap (CpStep.R' :: cp2)).cpring.map k)) := by
    rw [cpcolor1_R',
      ite_eq_right (by omega : ¬ (trace ((cpmap cp2).cpring.map k)).length ≤ 1), ← htr]
  refine ⟨?_, ?_⟩
  · rw [hstep]; exact hf.proper
  · rw [hstep]; exact hf.mem

/-! ### Correctness of the expansion

Expanding a `Y` or an `H` step into `U`, `K` and rotation steps leaves the
computed tree unchanged, as long as the trace it is applied to is `c0`-free —
which is exactly what the traces of colourings are. -/

private theorem notMem_zero_cons {a : Color} {u : List Color} (ha : a ≠ 0)
    (hu : (0 : Color) ∉ u) : (0 : Color) ∉ a :: u := by
  simp only [List.mem_cons, not_or]
  exact ⟨fun hc => ha hc.symm, hu⟩

private theorem ne_zero_of_notMem_zero {a : Color} {u : List Color}
    (h : (0 : Color) ∉ a :: u) : a ≠ 0 := fun hc => h (by rw [hc]; simp)

private theorem notMem_zero_of_cons {a : Color} {u : List Color}
    (h : (0 : Color) ∉ a :: u) : (0 : Color) ∉ u := fun hc => h (List.mem_cons_of_mem _ hc)

/-- Rotating `a :: u ++ [b]` all the way right brings `b` to the front. -/
theorem rotate_cons_concat {α : Type*} (a b : α) (u : List α) :
    (a :: (u ++ [b])).rotate (u.length + 1) = b :: a :: u := by
  rw [List.rotate_eq_drop_append_take
    (show u.length + 1 ≤ (a :: (u ++ [b])).length by simp)]
  simp

/-- The step functional only inspects its argument on `c0`-free traces. -/
theorem cpcolor1_congr {f g : List Color → Ctree} (s : CpStep)
    (h : ∀ u : List Color, (0 : Color) ∉ u → f u = g u) {et : List Color}
    (h0 : (0 : Color) ∉ et) : cpcolor1 s f et = cpcolor1 s g et := by
  have hrot : ∀ n : ℕ, (0 : Color) ∉ et.rotate n := fun n hc => h0 (List.mem_rotate.mp hc)
  cases s with
  | R n => exact h _ (hrot n)
  | R' =>
    rw [cpcolor1_R', cpcolor1_R']
    by_cases hl : et.length ≤ 1
    · rw [ite_eq_left hl, ite_eq_left hl]
    · rw [ite_eq_right hl, ite_eq_right hl, h _ (hrot _)]
  | U =>
    have hc : ∀ c : Color, c ≠ 0 → f (c :: c :: et) = g (c :: c :: et) :=
      fun c hcn => h _ (notMem_zero_cons hcn (notMem_zero_cons hcn h0))
    rw [cpcolor1_U, cpcolor1_U, hc c1 (by decide), hc c2 (by decide), hc c3 (by decide)]
  | Y =>
    cases et with
    | nil => rfl
    | cons e₁ et' =>
      have he : e₁ ≠ 0 := ne_zero_of_notMem_zero h0
      have h0' : (0 : Color) ∉ et' := notMem_zero_of_cons h0
      have hn : ∀ a b : Color, a ≠ 0 → b ≠ 0 → f (a :: b :: et') = g (a :: b :: et') :=
        fun a b ha hb => h _ (notMem_zero_cons ha (notMem_zero_cons hb h0'))
      rw [cpcolor1_Y_cons, cpcolor1_Y_cons,
        hn (e231 e₁) (e312 e₁) (by simpa using he) (by simpa using he),
        hn (e312 e₁) (e231 e₁) (by simpa using he) (by simpa using he)]
  | K =>
    match et with
    | [] => rfl
    | [_] => rfl
    | e₁ :: e₂ :: et' =>
      rw [cpcolor1_K_cons, cpcolor1_K_cons]
      by_cases he : e₁ = e₂
      · rw [ite_eq_left he, ite_eq_left he]
      · rw [ite_eq_right he, ite_eq_right he]
        exact h _ (notMem_zero_cons (fun hc => he (Color.add_eq_zero_iff.mp hc))
          (notMem_zero_of_cons (notMem_zero_of_cons h0)))
  | H =>
    match et with
    | [] => rfl
    | [_] => rfl
    | e₁ :: e₂ :: et' =>
      have he1 : e₁ ≠ 0 := ne_zero_of_notMem_zero h0
      have he2 : e₂ ≠ 0 := ne_zero_of_notMem_zero (notMem_zero_of_cons h0)
      have h0' : (0 : Color) ∉ et' := notMem_zero_of_cons (notMem_zero_of_cons h0)
      have hn : ∀ a b : Color, a ≠ 0 → b ≠ 0 → f (a :: b :: et') = g (a :: b :: et') :=
        fun a b ha hb => h _ (notMem_zero_cons ha (notMem_zero_cons hb h0'))
      rw [cpcolor1_H_cons, cpcolor1_H_cons]
      by_cases he : e₁ = e₂
      · rw [ite_eq_left he, ite_eq_left he,
          hn (e231 e₁) (e231 e₁) (by simpa using he1) (by simpa using he1),
          hn (e312 e₁) (e312 e₁) (by simpa using he1) (by simpa using he1)]
      · rw [ite_eq_right he, ite_eq_right he, hn e₂ e₁ he2 he1]
  | A =>
    match et with
    | [] => rfl
    | [_] => rfl
    | e₁ :: e₂ :: et' =>
      have he1 : e₁ ≠ 0 := ne_zero_of_notMem_zero h0
      have he2 : e₂ ≠ 0 := ne_zero_of_notMem_zero (notMem_zero_of_cons h0)
      have h0' : (0 : Color) ∉ et' := notMem_zero_of_cons (notMem_zero_of_cons h0)
      rw [cpcolor1_A_cons, cpcolor1_A_cons]
      by_cases he : e₁ = e₂
      · rw [ite_eq_left he, ite_eq_left he]
        cases et' with
        | nil =>
          exact h _ (notMem_zero_cons he1 (notMem_zero_cons he2 (by simp)))
        | cons e₃ et'' => exact h _ h0'
      · rw [ite_eq_right he, ite_eq_right he]

/-- The trace computation of a `U` step followed by a `K` step and rotations. -/
theorem cpexpandY_step (F : List Color → Ctree) (c e₁ : Color) (et : List Color) :
    cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .R' F)) (c :: c :: e₁ :: et)
      = if c = e₁ then .empty else F (c :: (c + e₁) :: et) := by
  have h1 : (c :: c :: e₁ :: et).rotate 1 = c :: e₁ :: (et ++ [c]) := by
    rw [List.rotate_cons_succ, List.rotate_zero]; rfl
  rw [cpcolor1_R, h1, cpcolor1_K_cons]
  by_cases hc : c = e₁
  · rw [ite_eq_left hc, ite_eq_left hc]
  · have hlen : ((c + e₁) :: (et ++ [c])).length = et.length + 2 := by simp
    rw [ite_eq_right hc, ite_eq_right hc, cpcolor1_R',
      ite_eq_right (show ¬ ((c + e₁) :: (et ++ [c])).length ≤ 1 by simp), hlen,
      show et.length + 2 - 1 = et.length + 1 from by omega, rotate_cons_concat]

/-- The `Y` expansion applied to a trace of length one. -/
theorem cpexpandY_step_nil (F : List Color → Ctree) (c : Color) :
    cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .R' F)) [c, c] = .empty := by
  have h1 : ([c, c] : List Color).rotate 1 = [c, c] := by
    rw [List.rotate_cons_succ, List.rotate_zero]; rfl
  rw [cpcolor1_R, h1, cpcolor1_K_cons, ite_eq_left rfl]

/-- The trace computation of a `U` step followed by two `K` steps and rotations. -/
theorem cpexpandH_step (F : List Color → Ctree) (c e₁ e₂ : Color) (et : List Color) :
    cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .K (cpcolor1 .R' F))) (c :: c :: e₁ :: e₂ :: et)
      = if c = e₁ then .empty else
          if c + e₁ = e₂ then .empty else F (c :: (c + e₁ + e₂) :: et) := by
  have h1 : (c :: c :: e₁ :: e₂ :: et).rotate 1 = c :: e₁ :: e₂ :: (et ++ [c]) := by
    rw [List.rotate_cons_succ, List.rotate_zero]; rfl
  rw [cpcolor1_R, h1, cpcolor1_K_cons]
  by_cases hc : c = e₁
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc, cpcolor1_K_cons]
    by_cases hc2 : c + e₁ = e₂
    · rw [ite_eq_left hc2, ite_eq_left hc2]
    · have hlen : ((c + e₁ + e₂) :: (et ++ [c])).length = et.length + 2 := by simp
      rw [ite_eq_right hc2, ite_eq_right hc2, cpcolor1_R',
        ite_eq_right (show ¬ ((c + e₁ + e₂) :: (et ++ [c])).length ≤ 1 by simp), hlen,
        show et.length + 2 - 1 = et.length + 1 from by omega, rotate_cons_concat]

/-- The `H` expansion applied to a trace of length one. -/
theorem cpexpandH_step_nil (F : List Color → Ctree) (c : Color) :
    cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .K (cpcolor1 .R' F))) [c, c] = .empty := by
  have h1 : ([c, c] : List Color).rotate 1 = [c, c] := by
    rw [List.rotate_cons_succ, List.rotate_zero]; rfl
  rw [cpcolor1_R, h1, cpcolor1_K_cons, ite_eq_left rfl]

/-- The `H` expansion applied to a trace of length two. -/
theorem cpexpandH_step_one (F : List Color → Ctree) (c e₁ : Color) (he : e₁ ≠ 0) :
    cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .K (cpcolor1 .R' F))) [c, c, e₁] = .empty := by
  have h1 : ([c, c, e₁] : List Color).rotate 1 = [c, e₁, c] := by
    rw [List.rotate_cons_succ, List.rotate_zero]; rfl
  rw [cpcolor1_R, h1, cpcolor1_K_cons]
  by_cases hc : c = e₁
  · rw [ite_eq_left hc]
  · have hne : ¬ (c + e₁ = c) := fun hcc => he (add_left_cancel (hcc.trans (add_zero c).symm))
    rw [ite_eq_right hc, cpcolor1_K_cons, ite_eq_right hne, cpcolor1_R',
      ite_eq_left (show ([c + e₁ + c] : List Color).length ≤ 1 by simp)]

/-- Expanding a `Y` step. -/
theorem cpcolor1Y_expand (F : List Color → Ctree) {et : List Color} (h0 : (0 : Color) ∉ et) :
    cpcolor1 .Y F et = cpcolor1 .U (cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .R' F))) et := by
  rw [cpcolor1_U]
  cases et with
  | nil =>
    rw [cpcolor1_Y_nil, cpexpandY_step_nil, cpexpandY_step_nil, cpexpandY_step_nil,
      Ctree.union_empty_left, Ctree.union_empty_left]
  | cons e₁ et' =>
    have he : e₁ ≠ 0 := ne_zero_of_notMem_zero h0
    rw [cpcolor1_Y_cons, cpexpandY_step, cpexpandY_step, cpexpandY_step]
    cases e₁ with
    | c0 => exact absurd rfl he
    | c1 =>
      change Ctree.union (F (c2 :: c3 :: et')) (F (c3 :: c2 :: et'))
        = Ctree.union Ctree.empty
            (Ctree.union (F (c2 :: c3 :: et')) (F (c3 :: c2 :: et')))
      rw [Ctree.union_empty_left]
    | c2 =>
      change Ctree.union (F (c3 :: c1 :: et')) (F (c1 :: c3 :: et'))
        = Ctree.union (F (c1 :: c3 :: et'))
            (Ctree.union Ctree.empty (F (c3 :: c1 :: et')))
      rw [Ctree.union_empty_left, Ctree.union_comm]
    | c3 =>
      change Ctree.union (F (c1 :: c2 :: et')) (F (c2 :: c1 :: et'))
        = Ctree.union (F (c1 :: c2 :: et'))
            (Ctree.union (F (c2 :: c1 :: et')) Ctree.empty)
      rw [Ctree.union_empty_right]

/-- Expanding an `H` step. -/
theorem cpcolor1H_expand (F : List Color → Ctree) {et : List Color} (h0 : (0 : Color) ∉ et) :
    cpcolor1 .H F et
      = cpcolor1 .U (cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .K (cpcolor1 .R' F)))) et := by
  rw [cpcolor1_U]
  match et with
  | [] =>
    rw [cpcolor1_H_nil, cpexpandH_step_nil, cpexpandH_step_nil, cpexpandH_step_nil,
      Ctree.union_empty_left, Ctree.union_empty_left]
  | [e₁] =>
    have he1 : e₁ ≠ 0 := ne_zero_of_notMem_zero h0
    rw [cpcolor1_H_singleton, cpexpandH_step_one F c1 e₁ he1,
      cpexpandH_step_one F c2 e₁ he1, cpexpandH_step_one F c3 e₁ he1,
      Ctree.union_empty_left, Ctree.union_empty_left]
  | e₁ :: e₂ :: et' =>
    have he1 : e₁ ≠ 0 := ne_zero_of_notMem_zero h0
    have he2 : e₂ ≠ 0 := ne_zero_of_notMem_zero (notMem_zero_of_cons h0)
    rw [cpexpandH_step, cpexpandH_step, cpexpandH_step]
    cases e₁ with
    | c0 => exact absurd rfl he1
    | c1 =>
      cases e₂ with
      | c0 => exact absurd rfl he2
      | c1 =>
        change Ctree.union (F (c2 :: c2 :: et')) (F (c3 :: c3 :: et'))
          = Ctree.union Ctree.empty
              (Ctree.union (F (c2 :: c2 :: et')) (F (c3 :: c3 :: et')))
        rw [Ctree.union_empty_left]
      | c2 =>
        change F (c2 :: c1 :: et')
          = Ctree.union Ctree.empty (Ctree.union (F (c2 :: c1 :: et')) Ctree.empty)
        rw [Ctree.union_empty_left, Ctree.union_empty_right]
      | c3 =>
        change F (c3 :: c1 :: et')
          = Ctree.union Ctree.empty (Ctree.union Ctree.empty (F (c3 :: c1 :: et')))
        rw [Ctree.union_empty_left, Ctree.union_empty_left]
    | c2 =>
      cases e₂ with
      | c0 => exact absurd rfl he2
      | c1 =>
        change F (c1 :: c2 :: et')
          = Ctree.union (F (c1 :: c2 :: et')) (Ctree.union Ctree.empty Ctree.empty)
        rw [Ctree.union_empty_left, Ctree.union_empty_right]
      | c2 =>
        change Ctree.union (F (c3 :: c3 :: et')) (F (c1 :: c1 :: et'))
          = Ctree.union (F (c1 :: c1 :: et'))
              (Ctree.union Ctree.empty (F (c3 :: c3 :: et')))
        rw [Ctree.union_empty_left, Ctree.union_comm]
      | c3 =>
        change F (c3 :: c2 :: et')
          = Ctree.union Ctree.empty (Ctree.union Ctree.empty (F (c3 :: c2 :: et')))
        rw [Ctree.union_empty_left, Ctree.union_empty_left]
    | c3 =>
      cases e₂ with
      | c0 => exact absurd rfl he2
      | c1 =>
        change F (c1 :: c3 :: et')
          = Ctree.union (F (c1 :: c3 :: et')) (Ctree.union Ctree.empty Ctree.empty)
        rw [Ctree.union_empty_left, Ctree.union_empty_right]
      | c2 =>
        change F (c2 :: c3 :: et')
          = Ctree.union Ctree.empty (Ctree.union (F (c2 :: c3 :: et')) Ctree.empty)
        rw [Ctree.union_empty_left, Ctree.union_empty_right]
      | c3 =>
        change Ctree.union (F (c1 :: c1 :: et')) (F (c2 :: c2 :: et'))
          = Ctree.union (F (c1 :: c1 :: et'))
              (Ctree.union (F (c2 :: c2 :: et')) Ctree.empty)
        rw [Ctree.union_empty_right]

/-- **Expanding the composite steps does not change the computed tree**, on the
`c0`-free traces the computation is applied to. -/
theorem foldr_cpcolor1_cpexpand : ∀ (cp : CProg) (f : List Color → Ctree) (et : List Color),
    (0 : Color) ∉ et →
    List.foldr cpcolor1 f cp.reverse et = List.foldr cpcolor1 f (cpexpand cp).reverse et := by
  intro cp
  induction cp using List.reverseRecOn with
  | nil => intro f et _; rfl
  | append_singleton cp s ih =>
    intro f et h0
    have hexp1 : cpexpand [s] = cpexpand1 s := by
      rw [cpexpand_cons, cpexpand_nil, List.append_nil]
    have hrev : (cp ++ [s]).reverse = s :: cp.reverse := by simp
    have hexp : (cpexpand (cp ++ [s])).reverse
        = (cpexpand1 s).reverse ++ (cpexpand cp).reverse := by
      rw [cpexpand_append, hexp1, List.reverse_append]
    rw [hrev, hexp, List.foldr_cons, List.foldr_append,
      cpcolor1_congr s (fun u hu => ih f u hu) h0]
    cases s with
    | R n => rfl
    | R' => rfl
    | U => rfl
    | K => rfl
    | A => rfl
    | Y =>
      rw [show (cpexpand1 CpStep.Y).reverse
        = [CpStep.U, CpStep.R 1, CpStep.K, CpStep.R'] from rfl]
      simp only [List.foldr_cons, List.foldr_nil]
      exact cpcolor1Y_expand _ h0
    | H =>
      rw [show (cpexpand1 CpStep.H).reverse
        = [CpStep.U, CpStep.R 1, CpStep.K, CpStep.K, CpStep.R'] from rfl]
      simp only [List.foldr_cons, List.foldr_nil]
      exact cpcolor1H_expand _ h0


/-! ### Transporting the invariant

The colouring invariant mentions the map a program builds only through its
darts, its ring and its dart injection, so it transports along an equality of
pointed maps.  Stating the transport with both maps as variables lets `subst`
do all the work; the two injections have to be compared with `HEq`, because
their types agree only once the maps have been identified. -/

/-- One construction step, as an operation on pointed maps. -/
noncomputable def stepMap : CpStep → PointedMap → PointedMap
  | .R n, M => M.ecpR n
  | .R', M => M.ecpR'
  | .Y, M => M.ecpY
  | .H, M => M.ecpH
  | .U, M => M.ecpU
  | .K, M => M.ecpK
  | .A, M => M.ecpA

/-- Running one more step of a program is applying `stepMap`. -/
theorem cpmap_cons_eq (s : CpStep) (cp : CProg) :
    cpmap (s :: cp) = stepMap s (cpmap cp) := by cases s <;> rfl

/-- One step turns equal maps into equal maps. -/
theorem cpmap_cons_congr (s : CpStep) {cpa cpb : CProg} (h : cpmap cpa = cpmap cpb) :
    cpmap (s :: cpa) = cpmap (s :: cpb) := by
  rw [cpmap_cons_eq, cpmap_cons_eq, h]

/-- Identified darts stay identified after adding a new dart. -/
theorem heq_icp.{u} {α β : Type u} (hαβ : α = β) {u : α} {v : β} (h : HEq u v) :
    HEq (EcpDart.icp u : EcpDart α) (EcpDart.icp v : EcpDart β) := by
  subst hαβ; rw [eq_of_heq h]

/-- A one-step dart injection respects an identification of the base maps. -/
theorem heq_injcpStep (s : CpStep) {cpa cpb : CProg} (hab : cpmap cpa = cpmap cpb)
    {u : (cpmap cpa).Dart} {v : (cpmap cpb).Dart} (huv : HEq u v) :
    HEq (injcpStep s cpa u) (injcpStep s cpb v) := by
  have hD : (cpmap cpa).Dart = (cpmap cpb).Dart := congrArg PointedMap.Dart hab
  cases s with
  | R n => exact huv
  | R' => exact huv
  | Y => exact heq_icp (congrArg EcpDart hD) (heq_icp hD huv)
  | H =>
    exact heq_icp (congrArg EcpDart (congrArg EcpDart hD))
      (heq_icp (congrArg EcpDart hD) (heq_icp hD huv))
  | U => exact heq_icp hD huv
  | K => exact heq_icp hD huv
  | A => exact huv

/-- Running a program on identified maps gives identified maps. -/
theorem cpmap_reverseAux_congr : ∀ (cp1 : CProg) {cpa cpb : CProg}, cpmap cpa = cpmap cpb →
    cpmap (cp1.reverseAux cpa) = cpmap (cp1.reverseAux cpb)
  | [], _, _, h => h
  | s :: cp1, _, _, h => cpmap_reverseAux_congr cp1 (cpmap_cons_congr s h)

/-- The dart injection of a program respects an identification of the base maps. -/
theorem heq_injcp : ∀ (cp1 : CProg) {cpa cpb : CProg}, cpmap cpa = cpmap cpb →
    ∀ {u : (cpmap cpa).Dart} {v : (cpmap cpb).Dart}, HEq u v →
    HEq (injcp cp1 cpa u) (injcp cp1 cpb v)
  | [], _, _, _, _, _, huv => huv
  | s :: cp1, _, _, hab, _, _, huv =>
      heq_injcp cp1 (cpmap_cons_congr s hab) (heq_injcpStep s hab huv)

/-- The colouring invariant, stated for an abstract base map, target map, dart
injection and tree.  This is the form in which it transports. -/
structure CpExtcolT (et0 : List Color) (N M : PointedMap) (h : N.Dart → M.Dart)
    (t : Ctree) (k : N.Dart → Color) : Prop where
  /-- The tree has the height predicted by the target ring. -/
  proper : Ctree.Proper (M.cpring.length - 2) t
  /-- It contains exactly the canonical tails of the extensions of `k`. -/
  mem : Ctree.mem t (normTail et0) = true ↔
      ∃ k0 : M.Dart → Color, M.map.Coloring k0 ∧
        normTail et0 = evenPartialTail ((M.cpring.map k0).rotate 1) ∧
        ∀ x, k0 (h x) = k x

/-- Reading the invariant of a program as an abstract invariant. -/
theorem CpExtcol.toT {et0 : List Color} {cp1 cp2 : CProg} {f : List Color → Ctree}
    {k : (cpmap cp2).Dart → Color} (H : CpExtcol et0 cp1 cp2 f k) :
    CpExtcolT et0 (cpmap cp2) (cpmap (cp1.reverseAux cp2)) (injcp cp1 cp2)
      (f (trace ((cpmap cp2).cpring.map k))) k := ⟨H.proper, H.mem⟩

/-- Reading an abstract invariant as the invariant of a program. -/
theorem CpExtcolT.ofT {et0 : List Color} {cp1 cp2 : CProg} {f : List Color → Ctree}
    {k : (cpmap cp2).Dart → Color}
    (H : CpExtcolT et0 (cpmap cp2) (cpmap (cp1.reverseAux cp2)) (injcp cp1 cp2)
      (f (trace ((cpmap cp2).cpring.map k))) k) : CpExtcol et0 cp1 cp2 f k :=
  ⟨H.proper, H.mem⟩

/-- **The invariant transports** along identifications of the base map, of the
target map, of the injection, of the colouring and of the tree. -/
theorem CpExtcolT.congr {et0 : List Color} {N N' M M' : PointedMap}
    {h : N.Dart → M.Dart} {h' : N'.Dart → M'.Dart} {t t' : Ctree}
    {k : N.Dart → Color} {k' : N'.Dart → Color}
    (hN : N = N') (hM : M = M')
    (hk : ∀ (x : N.Dart) (y : N'.Dart), HEq x y → k x = k' y)
    (hh : ∀ (x : N.Dart) (y : N'.Dart), HEq x y → HEq (h x) (h' y))
    (ht : t = t') (H : CpExtcolT et0 N M h t k) : CpExtcolT et0 N' M' h' t' k' := by
  subst hN; subst hM; subst ht
  have hkk : k = k' := funext fun x => hk x x HEq.rfl
  have hhh : h = h' := funext fun x => eq_of_heq (hh x x HEq.rfl)
  subst hkk; subst hhh
  exact H

/-! ### Colourings pulled back along the dart injections -/

namespace Hypermap

variable {D : Type*} {G : Hypermap D} {k : D → Color}

/-- Adjacent faces of a colouring have different colours. -/
theorem Coloring.ne_of_adj (hk : G.Coloring k) {x y : D} (h : G.Adj x y) : k x ≠ k y := by
  obtain ⟨z, hxz, hzy⟩ := h
  have h1 : k x = k z := hk.cface hxz
  have h2 : k (G.edge z) = k y := hk.cface hzy
  rw [h1, ← h2]
  exact (hk.edge z).symm

end Hypermap

/-- A colouring of an extended map is constant on the faces of the base map. -/
theorem cface_injcp_eq {cp1 cp2 : CProg} {k0 : (cpmap (cp1.reverseAux cp2)).Dart → Color}
    (hk0 : (cpmap (cp1.reverseAux cp2)).map.Coloring k0) {x y : (cpmap cp2).Dart}
    (h : (cpmap cp2).map.CFace x y) : k0 (injcp cp1 cp2 x) = k0 (injcp cp1 cp2 y) :=
  hk0.cface (sub_cface_injcp cp1 cp2 h)

/-- A colouring of an extended map separates the adjacent faces of the base map. -/
theorem adj_injcp_ne {cp1 cp2 : CProg} {k0 : (cpmap (cp1.reverseAux cp2)).Dart → Color}
    (hk0 : (cpmap (cp1.reverseAux cp2)).map.Coloring k0) {x y : (cpmap cp2).Dart}
    (h : (cpmap cp2).map.Adj x y) : k0 (injcp cp1 cp2 x) ≠ k0 (injcp cp1 cp2 y) :=
  hk0.ne_of_adj (sub_adj_injcp cp1 cp2 h)

/-! ### The first two entries of a ring trace -/

/-- The ring trace of a colouring, with its first two entries split off. -/
theorem trace_cpring_eq {M : PointedMap} {k : M.Dart → Color} (hk : M.map.Coloring k) :
    trace (M.cpring.map k)
      = (k (M.map.node M.point) + k M.point)
        :: (k M.point + k (M.map.node⁻¹ M.point))
        :: partialTrace ((M.cpring.drop 2 ++ [M.map.node M.point]).map k) := by
  have hprop : M.map.ProperCpring M.point := hk.properCpring _
  obtain ⟨d, hd⟩ : ∃ d, M.cpring.drop 2 = d := ⟨_, rfl⟩
  have hring : M.map.cpring M.point = M.map.node M.point :: M.point :: d := by
    rw [← hd]; exact Hypermap.head_proper_cpring hprop
  have hlen : (M.map.cpring M.point).length = d.length + 2 := by rw [hring]; simp
  rw [hd, show M.cpring = M.map.node M.point :: M.point :: d from hring,
    List.map_cons, List.map_cons, trace_cons, List.cons_append, pairmap_cons]
  cases d with
  | nil =>
    have hnl : ¬ M.map.LongCpring M.point := by
      intro hlong
      have h2 := Hypermap.long_cpring_iff.mp hlong
      rw [hlen] at h2
      simp at h2
    have hinv : M.map.node⁻¹ M.point = M.map.node M.point := by
      by_contra hcc
      exact hnl (Hypermap.longCpring_iff_inv_ne.mpr hcc)
    rw [hinv]
    rfl
  | cons c r =>
    have hlong : M.map.LongCpring M.point := by
      refine Hypermap.long_cpring_iff.mpr ?_
      rw [hlen]
      simp
    have h3 := Hypermap.head_long_cpring hlong
    rw [M.map.face_edge] at h3
    have heq2 := hring.symm.trans h3
    have hc : c = M.map.node⁻¹ M.point := by
      simp only [List.cons.injEq] at heq2
      exact heq2.2.2.1
    rw [hc]
    simp only [List.map_cons, List.map_append, List.cons_append, pairmap_cons]
    rfl


/-! ### The `U` step

A `U` step adds a disjoint new edge, hence a new face which meets the rest of
the map only along the face of `node x₀`.  A colouring of the extension is
therefore a colouring of the base map together with the colour of the new face,
which is `e + k (node x₀)` for one of the three nonzero offsets `e`; the ring
trace gains the two entries `e, e` in front. -/

namespace Hypermap

variable {D : Type*} (G : Hypermap D) (x₀ : D)

/-- The colouring of a `U` extension given by a colouring `k` of the base map
and the trace offset `e` of the new face. -/
def kU (k : D → Color) (e : Color) : EcpDart D → Color
  | .X => e + k (G.node x₀)
  | .Xe => k (G.node x₀)
  | .icp x => k x

@[simp] theorem kU_icp (k : D → Color) (e : Color) (x : D) :
    kU G x₀ k e (.icp x) = k x := rfl

@[simp] theorem kU_X (k : D → Color) (e : Color) :
    kU G x₀ k e .X = e + k (G.node x₀) := rfl

@[simp] theorem kU_Xe (k : D → Color) (e : Color) : kU G x₀ k e .Xe = k (G.node x₀) := rfl

variable {G x₀} [Finite D] [DecidableEq D]

omit [Finite D] in
/-- `kU` is constant on the faces of a `U` extension. -/
theorem kU_face {k : D → Color} (hk : G.Coloring k) (e : Color) (u : EcpDart D) :
    kU G x₀ k e (ecpUFace G x₀ u) = kU G x₀ k e u := by
  cases u with
  | X => rfl
  | Xe => rfl
  | icp y =>
    change kU G x₀ k e (if G.face y = G.node x₀ then .Xe else .icp (G.face y)) = k y
    by_cases h : G.face y = G.node x₀
    · rw [ite_eq_left h, kU_Xe, ← h, hk.face]
    · rw [ite_eq_right h, kU_icp, hk.face]

/-- `kU` is a colouring of the `U` extension as soon as the offset is nonzero. -/
theorem kU_coloring {k : D → Color} (hk : G.Coloring k) {e : Color} (he : e ≠ 0) :
    (ecpUMap G x₀).Coloring (kU G x₀ k e) where
  face u := kU_face hk e u
  edge u := by
    cases u with
    | X =>
      change kU G x₀ k e .Xe ≠ kU G x₀ k e .X
      rw [kU_X, kU_Xe]
      intro hc
      refine he (add_right_cancel (b := k (G.node x₀)) ?_)
      rw [zero_add]
      exact hc.symm
    | Xe =>
      change kU G x₀ k e .X ≠ kU G x₀ k e .Xe
      rw [kU_X, kU_Xe]
      intro hc
      refine he (add_right_cancel (b := k (G.node x₀)) ?_)
      rw [zero_add]
      exact hc
    | icp y => exact hk.edge y

end Hypermap

/-- Prefixing a colouring with the two darts of a new disjoint edge prefixes its
trace with two copies of the offset. -/
theorem trace_cons_cons_self (a e : Color) (t : List Color) :
    trace (a :: (e + a) :: a :: t) = e :: e :: trace (a :: t) := by
  rw [trace_cons, trace_cons, List.cons_append, pairmap_cons, List.cons_append, pairmap_cons,
    show a + (e + a) = e from by rw [add_comm e a, ← add_assoc, add_self, zero_add],
    show e + a + a = e from by rw [add_assoc, add_self, add_zero]]

namespace Hypermap

variable {D : Type*} [Finite D] [DecidableEq D] {G : Hypermap D} {x₀ : D}

/-- **The ring trace of a `U` extension** is the base trace with the offset
repeated in front. -/
theorem trace_cpring_ecpU (k : D → Color) (e : Color) :
    trace (((ecpUMap G x₀).cpring .X).map (kU G x₀ k e))
      = e :: e :: trace ((G.cpring x₀).map k) := by
  obtain ⟨t, ht⟩ : ∃ t, (G.cpring x₀).tail = t := ⟨_, rfl⟩
  have hring : G.cpring x₀ = G.node x₀ :: t := by rw [← ht]; exact head_cpring
  rw [cpring_ecpU, List.map_cons, List.map_cons, List.map_map, kU_X, kU_Xe,
    show (kU G x₀ k e ∘ EcpDart.icp) = k from rfl, hring, List.map_cons]
  exact trace_cons_cons_self _ _ _

end Hypermap

/-- The `U` extension colouring, for a `U` step of a construction program. -/
noncomputable def kUp (cp2 : CProg) (k : (cpmap cp2).Dart → Color) (e : Color) :
    (cpmap (CpStep.U :: cp2)).Dart → Color :=
  Hypermap.kU (cpmap cp2).map (cpmap cp2).point k e

@[simp] theorem kUp_icp (cp2 : CProg) (k : (cpmap cp2).Dart → Color) (e : Color)
    (x : (cpmap cp2).Dart) : kUp cp2 k e (.icp x) = k x := rfl

@[simp] theorem kUp_X (cp2 : CProg) (k : (cpmap cp2).Dart → Color) (e : Color) :
    kUp cp2 k e .X = e + k ((cpmap cp2).map.node (cpmap cp2).point) := rfl

@[simp] theorem kUp_Xe (cp2 : CProg) (k : (cpmap cp2).Dart → Color) (e : Color) :
    kUp cp2 k e .Xe = k ((cpmap cp2).map.node (cpmap cp2).point) := rfl

/-- The ring trace of a `U` step of a program. -/
theorem trace_cpring_ecpU' (cp2 : CProg) (k : (cpmap cp2).Dart → Color) (e : Color) :
    trace ((cpmap (CpStep.U :: cp2)).cpring.map
        (kUp cp2 k e))
      = e :: e :: trace ((cpmap cp2).cpring.map k) := Hypermap.trace_cpring_ecpU k e

/-- The `U` extension colouring is a colouring of the `U` step of a program. -/
theorem kU_coloring' {cp2 : CProg} {k : (cpmap cp2).Dart → Color}
    (hk : (cpmap cp2).map.Coloring k) {e : Color} (he : e ≠ 0) :
    (cpmap (CpStep.U :: cp2)).map.Coloring
      (kUp cp2 k e) := Hypermap.kU_coloring hk he

/-- The second new dart of a `U` step lies on the face of `node x₀`. -/
theorem cface_Xe_ecpU_cpmap (cp2 : CProg) :
    (cpmap (CpStep.U :: cp2)).map.CFace .Xe
      (.icp ((cpmap cp2).map.node (cpmap cp2).point)) :=
  (Hypermap.cface_Xe_icpU _ _ _).mpr (Equiv.Perm.SameCycle.refl _ _)

/-- The new face of a `U` step is adjacent to the face of `node x₀`. -/
theorem adj_X_ecpU_cpmap (cp2 : CProg) :
    (cpmap (CpStep.U :: cp2)).map.Adj .X
      (.icp ((cpmap cp2).map.node (cpmap cp2).point)) :=
  (Hypermap.adj_ecpU _ _ _).mpr
    ⟨_, List.mem_cons_self .., Equiv.Perm.SameCycle.refl _ _⟩

/-- **A `U` step**: the tree is the union of the three trees for the three
possible colours of the new face. -/
theorem cpcolor1U_correct (et0 : List Color) {cp1 cp2 : CProg} {f : List Color → Ctree}
    {k : (cpmap cp2).Dart → Color} (hk : (cpmap cp2).map.Coloring k)
    (hf : ∀ k' : (cpmap (CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.U :: cp2)).map.Coloring k' → CpExtcol et0 cp1 (CpStep.U :: cp2) f k') :
    CpExtcol et0 (CpStep.U :: cp1) cp2 (cpcolor1 .U f) k := by
  obtain ⟨et, het⟩ : ∃ et, trace ((cpmap cp2).cpring.map k) = et := ⟨_, rfl⟩
  have key : ∀ e : Color, e ≠ 0 →
      Ctree.Proper (cpHeight (cp1.reverseAux (CpStep.U :: cp2))) (f (e :: e :: et))
      ∧ (Ctree.mem (f (e :: e :: et)) (normTail et0) = true ↔
          ∃ k0 : (cpmap (cp1.reverseAux (CpStep.U :: cp2))).Dart → Color,
            (cpmap (cp1.reverseAux (CpStep.U :: cp2))).map.Coloring k0 ∧
              CpTrace0 et0 (cp1.reverseAux (CpStep.U :: cp2)) k0 ∧
              ∀ x, k0 (injcp cp1 (CpStep.U :: cp2) x) = kUp cp2 k e x) := by
    intro e he
    have h := hf _ (kU_coloring' hk he)
    have hp : Ctree.Proper (cpHeight (cp1.reverseAux (CpStep.U :: cp2)))
        (f (trace ((cpmap (CpStep.U :: cp2)).cpring.map (kUp cp2 k e)))) := h.proper
    have hm : Ctree.mem (f (trace ((cpmap (CpStep.U :: cp2)).cpring.map
          (kUp cp2 k e)))) (normTail et0) = true ↔
        ∃ k0 : (cpmap (cp1.reverseAux (CpStep.U :: cp2))).Dart → Color,
          (cpmap (cp1.reverseAux (CpStep.U :: cp2))).map.Coloring k0 ∧
            CpTrace0 et0 (cp1.reverseAux (CpStep.U :: cp2)) k0 ∧
            ∀ x, k0 (injcp cp1 (CpStep.U :: cp2) x) = kUp cp2 k e x := h.mem
    rw [trace_cpring_ecpU' cp2 k e, het] at hp hm
    exact ⟨hp, hm⟩
  have p1 := (key c1 (by decide)).1
  have p2 := (key c2 (by decide)).1
  have p3 := (key c3 (by decide)).1
  have hstep : cpcolor1 CpStep.U f et
      = Ctree.union (f (c1 :: c1 :: et))
          (Ctree.union (f (c2 :: c2 :: et)) (f (c3 :: c3 :: et))) := rfl
  refine ⟨?_, ?_⟩
  · rw [het, hstep]
    exact Ctree.union_proper _ _ _ p1 (Ctree.union_proper _ _ _ p2 p3)
  · rw [het, hstep, Ctree.mem_union _ _ _ _ p1 (Ctree.union_proper _ _ _ p2 p3),
      Ctree.mem_union _ _ _ _ p2 p3]
    constructor
    · intro hm
      have hone : ∃ e : Color, e ≠ 0 ∧ Ctree.mem (f (e :: e :: et)) (normTail et0) = true := by
        rcases Bool.or_eq_true_iff.mp hm with h | h
        · exact ⟨c1, by decide, h⟩
        · rcases Bool.or_eq_true_iff.mp h with h | h
          · exact ⟨c2, by decide, h⟩
          · exact ⟨c3, by decide, h⟩
      obtain ⟨e, he, hme⟩ := hone
      obtain ⟨k0, hk0, ht0, hkk⟩ := (key e he).2.mp hme
      exact ⟨k0, hk0, ht0, fun x => hkk (.icp x)⟩
    · rintro ⟨k0, hk0, ht0, hkk⟩
      have hXe : k0 (injcp cp1 (CpStep.U :: cp2) .Xe)
          = k ((cpmap cp2).map.node (cpmap cp2).point) := by
        rw [cface_injcp_eq (cp1 := cp1) (cp2 := CpStep.U :: cp2) hk0
          (cface_Xe_ecpU_cpmap cp2)]
        exact hkk _
      obtain ⟨e0, he0def⟩ : ∃ e0, k0 (injcp cp1 (CpStep.U :: cp2) .X)
          + k ((cpmap cp2).map.node (cpmap cp2).point) = e0 := ⟨_, rfl⟩
      have hne : e0 ≠ 0 := by
        have hd := adj_injcp_ne (cp1 := cp1) (cp2 := CpStep.U :: cp2) hk0
          (adj_X_ecpU_cpmap cp2)
        have hd2 : k0 (injcp cp1 (CpStep.U :: cp2) EcpDart.X)
            ≠ k ((cpmap cp2).map.node (cpmap cp2).point) := by
          rw [← hkk ((cpmap cp2).map.node (cpmap cp2).point)]
          exact hd
        intro hc
        exact hd2 (Color.add_eq_zero_iff.mp (he0def.trans hc))
      have hall : ∀ u, k0 (injcp cp1 (CpStep.U :: cp2) u) = kUp cp2 k e0 u := by
        intro u
        cases u with
        | X => rw [kUp_X, ← he0def, add_assoc, add_self, add_zero]
        | Xe => rw [kUp_Xe]; exact hXe
        | icp x => rw [kUp_icp]; exact hkk x
      have hmem := (key e0 hne).2.mpr ⟨k0, hk0, ht0, hall⟩
      cases he0 : e0 with
      | c0 => exact absurd he0 hne
      | c1 => rw [he0] at hmem; exact Bool.or_eq_true_iff.mpr (Or.inl hmem)
      | c2 =>
        rw [he0] at hmem
        exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.or_eq_true_iff.mpr (Or.inl hmem)))
      | c3 =>
        rw [he0] at hmem
        exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.or_eq_true_iff.mpr (Or.inr hmem)))


/-! ### The `K` step

A `K` step glues the faces of `node x₀` and of `node⁻¹ x₀` into one, and drops
the first two darts of the ring.  A colouring survives the step exactly when
those two faces already had the same colour, that is, when the first two entries
of the ring trace differ; the two entries are then replaced by their sum. -/

namespace Hypermap

variable {D : Type*} (G : Hypermap D) (x₀ : D)

/-- The colouring of a `K` extension induced by a colouring of the base map. -/
def kK (k : D → Color) : EcpDart D → Color
  | .X => k (G.node x₀)
  | .Xe => k (G.node⁻¹ x₀)
  | .icp y => k y

@[simp] theorem kK_icp (k : D → Color) (y : D) : kK G x₀ k (.icp y) = k y := rfl

@[simp] theorem kK_X (k : D → Color) : kK G x₀ k .X = k (G.node x₀) := rfl

@[simp] theorem kK_Xe (k : D → Color) : kK G x₀ k .Xe = k (G.node⁻¹ x₀) := rfl

variable {G x₀} [Finite D] [DecidableEq D]

omit [Finite D] in
/-- `kK` is constant on the faces of a `K` extension. -/
theorem kK_face {k : D → Color} (hk : G.Coloring k) (u : EcpDart D) :
    kK G x₀ k (ecpNFace G (G.node x₀) u) = kK G x₀ k u := by
  have hb : G.node⁻¹ (G.node x₀) = x₀ := G.inv_node_node x₀
  cases u with
  | X => rfl
  | Xe =>
    rw [ecpNFace_Xe, hb]
    by_cases h : x₀ = G.node (G.node x₀)
    · have hinv : G.node⁻¹ x₀ = G.node x₀ := by
        conv_lhs => rw [h]
        exact G.inv_node_node _
      rw [ite_eq_left h, kK_X, kK_Xe, hinv]
    · rw [ite_eq_right h, kK_icp, kK_Xe]
  | icp y =>
    rw [ecpNFace_icp, hb]
    by_cases h1 : y = G.edge x₀
    · rw [ite_eq_left h1, kK_Xe, kK_icp, h1, ← G.face_edge x₀, hk.face]
    · rw [ite_eq_right h1]
      by_cases h2 : y = G.edge (G.node (G.node x₀))
      · have hf : G.face y = G.node x₀ := by
          rw [h2, G.face_edge, G.inv_node_node]
        rw [ite_eq_left h2, kK_X, kK_icp, ← hf, hk.face]
      · rw [ite_eq_right h2, kK_icp, kK_icp, hk.face]

/-- `kK` is a colouring of the `K` extension exactly when the two faces glued by
the step already had the same colour. -/
theorem kK_coloring {k : D → Color} (hk : G.Coloring k)
    (hne : k (G.node x₀) ≠ k (G.node⁻¹ x₀)) {y : D} (hy : y = G.node x₀) :
    (ecpNMap G y).Coloring (kK G x₀ k) := by
  subst hy
  refine ⟨?_, fun u => kK_face hk u⟩
  intro u
  cases u with
  | X => exact fun hc => hne hc.symm
  | Xe => exact hne
  | icp y => exact hk.edge y

omit [DecidableEq D] in
/-- The ring of a nontrivial map, past its first two darts, either is empty (and
then the two ring neighbours of `x₀` coincide) or starts at `node⁻¹ x₀`. -/
theorem drop2_cpring (hp : G.ProperCpring x₀) :
    ((G.cpring x₀).drop 2 = [] ∧ G.node⁻¹ x₀ = G.node x₀)
      ∨ ∃ r, (G.cpring x₀).drop 2 = G.node⁻¹ x₀ :: r := by
  obtain ⟨d, hd⟩ : ∃ d, (G.cpring x₀).drop 2 = d := ⟨_, rfl⟩
  have hring : G.cpring x₀ = G.node x₀ :: x₀ :: d := by
    rw [← hd]; exact head_proper_cpring hp
  have hlen : (G.cpring x₀).length = d.length + 2 := by rw [hring]; simp
  cases d with
  | nil =>
    refine Or.inl ⟨hd, ?_⟩
    have hnl : ¬ G.LongCpring x₀ := by
      intro hl
      have h2 := long_cpring_iff.mp hl
      rw [hlen] at h2
      simp at h2
    by_contra hc
    exact hnl (longCpring_iff_inv_ne.mpr hc)
  | cons c r =>
    have hlong : G.LongCpring x₀ := by
      refine long_cpring_iff.mpr ?_
      rw [hlen]
      simp
    have h3 := head_long_cpring hlong
    rw [G.face_edge] at h3
    have heq2 := hring.symm.trans h3
    have hc : c = G.node⁻¹ x₀ := by
      simp only [List.cons.injEq] at heq2
      exact heq2.2.2.1
    exact Or.inr ⟨r, by rw [hd, hc]⟩

/-- **The ring trace of a `K` extension**: the first two entries of the base
trace are replaced by their sum. -/
theorem trace_cpring_ecpK {k : D → Color} (_hk : G.Coloring k) (hp : G.ProperCpring x₀)
    {y : D} (hy : y = G.node x₀) {z : EcpDart D} (hz : z = (ecpNMap G y).node⁻¹ .X) :
    trace (((ecpNMap G y).cpring z).map (kK G x₀ k))
      = (k (G.node x₀) + k (G.node⁻¹ x₀))
        :: partialTrace (((G.cpring x₀).drop 2 ++ [G.node x₀]).map k) := by
  subst hy
  subst hz
  rw [cpring_ecpK G x₀ hp, List.map_cons, List.map_map, kK_X,
    show (kK G x₀ k ∘ EcpDart.icp) = k from rfl]
  rcases drop2_cpring hp with ⟨hnil, hinv⟩ | ⟨r, hr⟩
  · rw [hnil, hinv, List.map_nil, trace_cons]
    rfl
  · rw [hr, trace_cons]
    simp only [List.map_cons, List.map_append, List.cons_append, pairmap_cons]
    rfl

end Hypermap

/-- The colouring of a `K` step of a program induced by a colouring of the base
map. -/
noncomputable def kKp (cp2 : CProg) (k : (cpmap cp2).Dart → Color) :
    (cpmap (CpStep.K :: cp2)).Dart → Color :=
  Hypermap.kK (cpmap cp2).map (cpmap cp2).point k

@[simp] theorem kKp_icp (cp2 : CProg) (k : (cpmap cp2).Dart → Color) (x : (cpmap cp2).Dart) :
    kKp cp2 k (.icp x) = k x := rfl

@[simp] theorem kKp_X (cp2 : CProg) (k : (cpmap cp2).Dart → Color) :
    kKp cp2 k .X = k ((cpmap cp2).map.node (cpmap cp2).point) := rfl

/-- `kKp` is a colouring of the `K` step when the two glued faces had the same
colour. -/
theorem kKp_coloring {cp2 : CProg} {k : (cpmap cp2).Dart → Color}
    (hk : (cpmap cp2).map.Coloring k)
    (hne : k ((cpmap cp2).map.node (cpmap cp2).point)
      ≠ k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)) :
    (cpmap (CpStep.K :: cp2)).map.Coloring (kKp cp2 k) :=
  Hypermap.kK_coloring hk hne (PointedMap.point_ecpR' (cpmap cp2))

/-- The ring trace of a `K` step of a program. -/
theorem trace_cpring_ecpK' (cp2 : CProg) {k : (cpmap cp2).Dart → Color}
    (hk : (cpmap cp2).map.Coloring k) :
    trace ((cpmap (CpStep.K :: cp2)).cpring.map (kKp cp2 k))
      = (k ((cpmap cp2).map.node (cpmap cp2).point)
          + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point))
        :: partialTrace (((cpmap cp2).cpring.drop 2
            ++ [(cpmap cp2).map.node (cpmap cp2).point]).map k) :=
  Hypermap.trace_cpring_ecpK hk (hk.properCpring _) (PointedMap.point_ecpR' (cpmap cp2))
    (PointedMap.point_ecpK (cpmap cp2))

/-- The two faces glued by a `K` step are adjacent after the step. -/
theorem adj_icpK_cpmap (cp2 : CProg) :
    (cpmap (CpStep.K :: cp2)).map.Adj
      (.icp ((cpmap cp2).map.node⁻¹ (cpmap cp2).point))
      (.icp ((cpmap cp2).map.node (cpmap cp2).point)) :=
  (PointedMap.adj_icpK (cpmap cp2) _ _).mpr
    (Or.inr (Or.inl ⟨Equiv.Perm.SameCycle.refl _ _, Equiv.Perm.SameCycle.refl _ _⟩))

/-- Every dart of a `K` step lies on the face of an old dart. -/
theorem fband_icpK_cpmap (cp2 : CProg) (u : (cpmap (CpStep.K :: cp2)).Dart) :
    ∃ x : (cpmap cp2).Dart, (cpmap (CpStep.K :: cp2)).map.CFace u (.icp x) :=
  PointedMap.fband_icpK (cpmap cp2) u

/-- **A `K` step**: the tree is empty when the two glued faces would clash, and
otherwise the tree of the trace with its first two entries added together. -/
theorem cpcolor1K_correct (et0 : List Color) {cp1 cp2 : CProg} {f : List Color → Ctree}
    {k : (cpmap cp2).Dart → Color} (hk : (cpmap cp2).map.Coloring k)
    (hf : ∀ k' : (cpmap (CpStep.K :: cp2)).Dart → Color,
      (cpmap (CpStep.K :: cp2)).map.Coloring k' → CpExtcol et0 cp1 (CpStep.K :: cp2) f k') :
    CpExtcol et0 (CpStep.K :: cp1) cp2 (cpcolor1 .K f) k := by
  obtain ⟨et2, het2⟩ : ∃ et2, partialTrace (((cpmap cp2).cpring.drop 2
      ++ [(cpmap cp2).map.node (cpmap cp2).point]).map k) = et2 := ⟨_, rfl⟩
  have htr : trace ((cpmap cp2).cpring.map k)
      = (k ((cpmap cp2).map.node (cpmap cp2).point) + k (cpmap cp2).point)
        :: (k (cpmap cp2).point + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)) :: et2 := by
    rw [← het2]; exact trace_cpring_eq hk
  by_cases hcase : k ((cpmap cp2).map.node (cpmap cp2).point) + k (cpmap cp2).point
      = k (cpmap cp2).point + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)
  · have hsame : k ((cpmap cp2).map.node (cpmap cp2).point)
        = k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point) := by
      have h := hcase
      rw [add_comm (k ((cpmap cp2).map.node (cpmap cp2).point))] at h
      exact add_left_cancel h
    refine ⟨?_, ?_⟩
    · rw [htr, cpcolor1_K_cons, ite_eq_left hcase]
      trivial
    · rw [htr, cpcolor1_K_cons, ite_eq_left hcase, Ctree.mem_empty]
      constructor
      · intro hcon; exact absurd hcon (by simp)
      · rintro ⟨k0, hk0, -, hkk⟩
        have hd := adj_injcp_ne (cp1 := cp1) (cp2 := CpStep.K :: cp2) hk0
          (adj_icpK_cpmap cp2)
        have h1 : k0 (injcp cp1 (CpStep.K :: cp2)
            (.icp ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)))
            = k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point) :=
          hkk ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)
        have h2 : k0 (injcp cp1 (CpStep.K :: cp2)
            (.icp ((cpmap cp2).map.node (cpmap cp2).point)))
            = k ((cpmap cp2).map.node (cpmap cp2).point) :=
          hkk ((cpmap cp2).map.node (cpmap cp2).point)
        rw [h1, h2] at hd
        exact absurd hsame.symm hd
  · have hne : k ((cpmap cp2).map.node (cpmap cp2).point)
        ≠ k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point) := by
      intro hc
      exact hcase (by rw [hc, add_comm])
    have hcol : (cpmap (CpStep.K :: cp2)).map.Coloring (kKp cp2 k) := kKp_coloring hk hne
    have h := hf _ hcol
    have htrK : trace ((cpmap (CpStep.K :: cp2)).cpring.map (kKp cp2 k))
        = (k ((cpmap cp2).map.node (cpmap cp2).point)
            + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)) :: et2 := by
      rw [trace_cpring_ecpK' cp2 hk, het2]
    have hsum : (k ((cpmap cp2).map.node (cpmap cp2).point) + k (cpmap cp2).point)
        + (k (cpmap cp2).point + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point))
        = k ((cpmap cp2).map.node (cpmap cp2).point)
          + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point) := by
      rw [add_comm (k (cpmap cp2).point)
        (k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)), add_add_add_comm, add_self, add_zero]
    have hp : Ctree.Proper (cpHeight (cp1.reverseAux (CpStep.K :: cp2)))
        (f (trace ((cpmap (CpStep.K :: cp2)).cpring.map (kKp cp2 k)))) := h.proper
    have hm : Ctree.mem (f (trace ((cpmap (CpStep.K :: cp2)).cpring.map
          (kKp cp2 k)))) (normTail et0) = true ↔
        ∃ k0 : (cpmap (cp1.reverseAux (CpStep.K :: cp2))).Dart → Color,
          (cpmap (cp1.reverseAux (CpStep.K :: cp2))).map.Coloring k0 ∧
            CpTrace0 et0 (cp1.reverseAux (CpStep.K :: cp2)) k0 ∧
            ∀ x, k0 (injcp cp1 (CpStep.K :: cp2) x) = kKp cp2 k x := h.mem
    rw [htrK] at hp hm
    refine ⟨?_, ?_⟩
    · rw [htr, cpcolor1_K_cons, ite_eq_right hcase, hsum]
      exact hp
    · rw [htr, cpcolor1_K_cons, ite_eq_right hcase, hsum, hm]
      constructor
      · rintro ⟨k0, hk0, ht0, hkk⟩
        exact ⟨k0, hk0, ht0, fun x => hkk (.icp x)⟩
      · rintro ⟨k0, hk0, ht0, hkk⟩
        refine ⟨k0, hk0, ht0, ?_⟩
        intro u
        obtain ⟨x, hx⟩ := fband_icpK_cpmap cp2 u
        rw [cface_injcp_eq (cp1 := cp1) (cp2 := CpStep.K :: cp2) hk0 hx, hcol.cface hx]
        exact hkk x

/-! ### The `A` step

An `A` step merges the two ring neighbours of `x₀` into one face; a colouring
survives exactly when they already had the same colour, that is, when the first
two entries of the ring trace agree.  The colouring itself is unchanged, and the
ring loses its first two darts unless it had only two. -/

namespace Hypermap

variable {D : Type*} [Finite D] [DecidableEq D] {G : Hypermap D} {x₀ : D}

omit [Finite D] in
/-- An `A` step keeps a colouring apart across every hyperedge. -/
theorem kA_edge {k : D → Color} (hk : G.Coloring k) (x : D) :
    k (ecpAEdge G x₀ x) ≠ k x := by
  unfold ecpAEdge
  by_cases hcf : G.CFace (G.edge x₀) (G.node x₀)
  · rw [ite_eq_left hcf]
    by_cases h1 : x = x₀
    · have hb : k (G.node x₀) = k (G.edge (G.node (G.node x₀))) := by
        have h := hk.face (G.edge (G.node (G.node x₀)))
        rw [G.nodeK (G.node x₀)] at h
        exact h
      rw [ite_eq_left h1, h1, ← hb]
      exact fun hc => hk.ne_node x₀ hc.symm
    · rw [ite_eq_right h1]
      by_cases h2 : x = G.node (G.node x₀)
      · rw [ite_eq_left h2, h2, hk.cface hcf]
        exact hk.ne_node (G.node x₀)
      · rw [ite_eq_right h2]
        exact hk.edge x
  · rw [ite_eq_right hcf]
    exact hk.edge x

/-- A colouring that identifies the two merged faces is constant on the faces of
the `A` extension. -/
theorem kA_cface {k : D → Color} (hk : G.Coloring k)
    (hsame : k (G.node x₀) = k (G.node⁻¹ x₀)) {x y : D}
    (h : (ecpAMap G x₀).CFace x y) : k x = k y := by
  rcases (cface_icpA G x₀ x y).mp h with hc | ⟨hx, hy⟩
  · exact hk.cface hc
  · have hx' : k x = k (G.node x₀) := by
      rcases hx with hx | hx
      · exact hk.cface hx
      · rw [hk.cface hx, ← hsame]
    have hy' : k y = k (G.node x₀) := by
      rcases hy with hy | hy
      · exact hk.cface hy
      · rw [hk.cface hy, ← hsame]
    rw [hx', hy']

/-- **A colouring survives an `A` step** exactly when the two merged faces
already had the same colour. -/
theorem kA_coloring {k : D → Color} (hk : G.Coloring k)
    (hsame : k (G.node x₀) = k (G.node⁻¹ x₀)) : (ecpAMap G x₀).Coloring k where
  edge x := kA_edge hk x
  face x := (kA_cface hk hsame ((ecpAMap G x₀).cface_face x)).symm

end Hypermap

/-- A colouring survives an `A` step of a program when the two merged faces had
the same colour. -/
theorem kA_coloring' {cp2 : CProg} {k : (cpmap cp2).Dart → Color}
    (hk : (cpmap cp2).map.Coloring k)
    (hsame : k ((cpmap cp2).map.node (cpmap cp2).point)
      = k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)) :
    (cpmap (CpStep.A :: cp2)).map.Coloring k := Hypermap.kA_coloring hk hsame

/-- The two merged faces of an `A` step lie on a common face afterwards. -/
theorem cface_ecpA_cpmap (cp2 : CProg) :
    (cpmap (CpStep.A :: cp2)).map.CFace ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)
      ((cpmap cp2).map.node (cpmap cp2).point) :=
  Hypermap.ecpA_merge _ _

/-- The ring trace after an `A` step at a long ring. -/
theorem trace_cpring_ecpA_long (cp2 : CProg) (k : (cpmap cp2).Dart → Color)
    (h : (cpmap cp2).Long) :
    trace ((cpmap (CpStep.A :: cp2)).cpring.map k)
      = trace (((cpmap cp2).cpring.drop 2).map k) :=
  congrArg (fun l : List (cpmap cp2).Dart => trace (l.map k))
    (PointedMap.cpring_ecpA_of_long (cpmap cp2) h)

/-- The ring trace after an `A` step at a short ring. -/
theorem trace_cpring_ecpA_short (cp2 : CProg) (k : (cpmap cp2).Dart → Color)
    (h : ¬ (cpmap cp2).Long) :
    trace ((cpmap (CpStep.A :: cp2)).cpring.map k)
      = trace ((cpmap cp2).cpring.map k) :=
  congrArg (fun l : List (cpmap cp2).Dart => trace (l.map k))
    (PointedMap.cpring_ecpA_of_not_long (cpmap cp2) h)

/-- **An `A` step**: the tree is empty when the two merged faces would clash, and
otherwise the tree of the trace with its first two entries dropped. -/
theorem cpcolor1A_correct (et0 : List Color) {cp1 cp2 : CProg} {f : List Color → Ctree}
    {k : (cpmap cp2).Dart → Color} (hk : (cpmap cp2).map.Coloring k)
    (hf : ∀ k' : (cpmap (CpStep.A :: cp2)).Dart → Color,
      (cpmap (CpStep.A :: cp2)).map.Coloring k' → CpExtcol et0 cp1 (CpStep.A :: cp2) f k') :
    CpExtcol et0 (CpStep.A :: cp1) cp2 (cpcolor1 .A f) k := by
  have hp : (cpmap cp2).map.ProperCpring (cpmap cp2).point := hk.properCpring _
  obtain ⟨et2, het2⟩ : ∃ et2, partialTrace (((cpmap cp2).cpring.drop 2
      ++ [(cpmap cp2).map.node (cpmap cp2).point]).map k) = et2 := ⟨_, rfl⟩
  have htr : trace ((cpmap cp2).cpring.map k)
      = (k ((cpmap cp2).map.node (cpmap cp2).point) + k (cpmap cp2).point)
        :: (k (cpmap cp2).point + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)) :: et2 := by
    rw [← het2]; exact trace_cpring_eq hk
  by_cases hcase : k ((cpmap cp2).map.node (cpmap cp2).point) + k (cpmap cp2).point
      = k (cpmap cp2).point + k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)
  · have hsame : k ((cpmap cp2).map.node (cpmap cp2).point)
        = k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point) := by
      have h := hcase
      rw [add_comm (k ((cpmap cp2).map.node (cpmap cp2).point))] at h
      exact add_left_cancel h
    have h := hf k (kA_coloring' hk hsame)
    have hlen : ((cpmap cp2).cpring.drop 2).length
        = (cpmap cp2).cpring.length - 2 := by simp
    have hstep : cpcolor1 CpStep.A f (trace ((cpmap cp2).cpring.map k))
        = f (trace ((cpmap (CpStep.A :: cp2)).cpring.map k)) := by
      rcases Hypermap.drop2_cpring hp with ⟨hnil, -⟩ | ⟨r, hr⟩
      · have hdrop : (cpmap cp2).cpring.drop 2 = [] := hnil
        have hz : et2 = [] := by rw [← het2, hdrop]; rfl
        have hnl : ¬ (cpmap cp2).Long := by
          intro hlong
          have h2 := (PointedMap.long_iff (cpmap cp2)).mp hlong
          rw [hdrop] at hlen
          simp only [List.length_nil] at hlen
          omega
        rw [trace_cpring_ecpA_short cp2 k hnl, htr, hz, cpcolor1_A_cons, ite_eq_left hcase]
      · have hdrop : (cpmap cp2).cpring.drop 2
            = (cpmap cp2).map.node⁻¹ (cpmap cp2).point :: r := hr
        have hl : (cpmap cp2).Long := by
          refine (PointedMap.long_iff (cpmap cp2)).mpr ?_
          rw [hdrop] at hlen
          simp only [List.length_cons] at hlen
          omega
        have hcons : et2 = pairmap (· + ·) (k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point))
            ((r ++ [(cpmap cp2).map.node (cpmap cp2).point]).map k) := by
          rw [← het2, hdrop]; rfl
        have htrA : trace ((cpmap (CpStep.A :: cp2)).cpring.map k) = et2 := by
          rw [trace_cpring_ecpA_long cp2 k hl, hdrop, List.map_cons, trace_cons, hcons,
            ← hsame]
          simp only [List.map_append, List.map_cons, List.map_nil]
        obtain ⟨a2, t2, ht2⟩ : ∃ a2 t2, et2 = a2 :: t2 := by
          rw [hcons]
          cases r with
          | nil => exact ⟨_, _, rfl⟩
          | cons b r' => exact ⟨_, _, rfl⟩
        rw [htrA, htr, ht2, cpcolor1_A_cons, ite_eq_left hcase]
    exact ⟨by rw [hstep]; exact h.proper, by rw [hstep]; exact h.mem⟩
  · refine ⟨?_, ?_⟩
    · rw [htr, cpcolor1_A_cons, ite_eq_right hcase]
      trivial
    · rw [htr, cpcolor1_A_cons, ite_eq_right hcase, Ctree.mem_empty]
      constructor
      · intro hcon; exact absurd hcon (by simp)
      · rintro ⟨k0, hk0, -, hkk⟩
        refine absurd ?_ hcase
        have h1 : k0 (injcp cp1 (CpStep.A :: cp2)
            ((cpmap cp2).map.node⁻¹ (cpmap cp2).point))
            = k ((cpmap cp2).map.node⁻¹ (cpmap cp2).point) :=
          hkk ((cpmap cp2).map.node⁻¹ (cpmap cp2).point)
        have h2 : k0 (injcp cp1 (CpStep.A :: cp2)
            ((cpmap cp2).map.node (cpmap cp2).point))
            = k ((cpmap cp2).map.node (cpmap cp2).point) :=
          hkk ((cpmap cp2).map.node (cpmap cp2).point)
        have hc := cface_injcp_eq (cp1 := cp1) (cp2 := CpStep.A :: cp2) hk0
          (cface_ecpA_cpmap cp2)
        rw [h1, h2] at hc
        rw [← hc, add_comm]


/-! ### The `Y` and `H` steps

A `Y` step is a `U` step followed by a `K` step, up to rotations, and an `H`
step is a `U` step followed by two `K` steps.  The expanded program builds the
same map, with the same dart injection, so the invariant for the expansion is
the invariant for the composite step. -/

/-- Equal pointed maps with matching colourings have equal ring traces. -/
theorem heq_trace_cpring_map {N N' : PointedMap} (hN : N = N') {k : N.Dart → Color}
    {k' : N'.Dart → Color} (hk : ∀ (x : N.Dart) (y : N'.Dart), HEq x y → k x = k' y) :
    trace (N.cpring.map k) = trace (N'.cpring.map k') := by
  subst hN
  have hkk : k = k' := funext fun x => hk x x HEq.rfl
  subst hkk
  rfl

/-- A colouring transports along an equality of pointed maps. -/
theorem coloring_pmap_congr {N N' : PointedMap} (hN : N = N') {k : N.Dart → Color}
    {k' : N'.Dart → Color} (hk : ∀ (x : N.Dart) (y : N'.Dart), HEq x y → k x = k' y)
    (h : N.map.Coloring k) : N'.map.Coloring k' := by
  subst hN
  have hkk : k = k' := funext fun x => hk x x HEq.rfl
  subst hkk
  exact h

/-- The invariant transports along a change of the base program that builds the
same map. -/
theorem cpExtcol_base_congr (et0 : List Color) (cp1 : CProg) {cpa cpb : CProg}
    (hab : cpmap cpa = cpmap cpb) {f : List Color → Ctree}
    {ka : (cpmap cpa).Dart → Color} {kb : (cpmap cpb).Dart → Color}
    (hk : ∀ (x : (cpmap cpb).Dart) (y : (cpmap cpa).Dart), HEq x y → kb x = ka y)
    (H : CpExtcol et0 cp1 cpb f kb) : CpExtcol et0 cp1 cpa f ka :=
  CpExtcolT.ofT (H.toT.congr hab.symm (cpmap_reverseAux_congr cp1 hab.symm) hk
    (fun _ _ hxy => heq_injcp cp1 hab.symm hxy) (congrArg f (heq_trace_cpring_map hab.symm hk)))

/-- The invariant transports along a change of the outermost steps of a program
that build the same map with the same dart injection. -/
theorem cpExtcol_head_congr (et0 : List Color) (cp1 cp2 : CProg) {cpa cpb : CProg}
    (hab : cpmap cpa = cpmap cpb)
    {a : (cpmap cp2).Dart → (cpmap cpa).Dart} {b : (cpmap cp2).Dart → (cpmap cpb).Dart}
    (hb : ∀ x, HEq (a x) (b x)) {f g : List Color → Ctree} {k : (cpmap cp2).Dart → Color}
    (hfg : f (trace ((cpmap cp2).cpring.map k)) = g (trace ((cpmap cp2).cpring.map k)))
    (H : CpExtcolT et0 (cpmap cp2) (cpmap (cp1.reverseAux cpa))
        (fun x => injcp cp1 cpa (a x)) (f (trace ((cpmap cp2).cpring.map k))) k) :
    CpExtcolT et0 (cpmap cp2) (cpmap (cp1.reverseAux cpb))
        (fun x => injcp cp1 cpb (b x)) (g (trace ((cpmap cp2).cpring.map k))) k :=
  H.congr rfl (cpmap_reverseAux_congr cp1 hab)
    (fun x y hxy => by rw [eq_of_heq hxy])
    (fun x y hxy => by
      rw [← eq_of_heq hxy]
      exact heq_injcp cp1 hab (hb x)) hfg

/-- **A `Y` step**, obtained by expanding it into a `U` step, a `K` step and two
rotations. -/
theorem cpcolor1Y_correct (et0 : List Color) {cp1 cp2 : CProg} {f : List Color → Ctree}
    {k : (cpmap cp2).Dart → Color} (hk : (cpmap cp2).map.Coloring k)
    (hf : ∀ k' : (cpmap (CpStep.Y :: cp2)).Dart → Color,
      (cpmap (CpStep.Y :: cp2)).map.Coloring k' → CpExtcol et0 cp1 (CpStep.Y :: cp2) f k') :
    CpExtcol et0 (CpStep.Y :: cp1) cp2 (cpcolor1 .Y f) k := by
  have hAB : cpmap (CpStep.R' :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)
      = cpmap (CpStep.Y :: cp2) := cpmap_expand_Y cp2
  have hf' : ∀ k4 : (cpmap (CpStep.R' :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).Dart
        → Color,
      (cpmap (CpStep.R' :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).map.Coloring k4 →
      CpExtcol et0 cp1 (CpStep.R' :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2) f k4 := by
    intro k4 hk4
    refine cpExtcol_base_congr et0 cp1 hAB (fun x y hxy => by rw [eq_of_heq hxy])
      (hf k4 (coloring_pmap_congr hAB (fun x y hxy => by rw [eq_of_heq hxy]) hk4))
  have hR' : ∀ k3 : (cpmap (CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).map.Coloring k3 →
      CpExtcol et0 (CpStep.R' :: cp1) (CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)
        (cpcolor1 .R' f) k3 :=
    fun k3 hk3 => cpcolor1R'_correct et0 hk3 (hf' k3 hk3)
  have hK : ∀ k2 : (cpmap (CpStep.R 1 :: CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.R 1 :: CpStep.U :: cp2)).map.Coloring k2 →
      CpExtcol et0 (CpStep.K :: CpStep.R' :: cp1) (CpStep.R 1 :: CpStep.U :: cp2)
        (cpcolor1 .K (cpcolor1 .R' f)) k2 :=
    fun k2 hk2 => cpcolor1K_correct et0 hk2 hR'
  have hR1 : ∀ k1 : (cpmap (CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.U :: cp2)).map.Coloring k1 →
      CpExtcol et0 (CpStep.R 1 :: CpStep.K :: CpStep.R' :: cp1) (CpStep.U :: cp2)
        (cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .R' f))) k1 :=
    fun k1 hk1 => cpcolor1R_correct et0 1 (hK k1 hk1)
  have hU := cpcolor1U_correct et0 hk hR1
  have h0 : (0 : Color) ∉ trace ((cpmap cp2).cpring.map k) := hk.zero_notMem_trace_cpring _
  exact CpExtcolT.ofT (cpExtcol_head_congr et0 cp1 cp2 hAB
    (fun x => heq_of_eq (injcp_expand_Y cp2 x)) (cpcolor1Y_expand f h0).symm hU.toT)

/-- **An `H` step**, obtained by expanding it into a `U` step, two `K` steps and
two rotations. -/
theorem cpcolor1H_correct (et0 : List Color) {cp1 cp2 : CProg} {f : List Color → Ctree}
    {k : (cpmap cp2).Dart → Color} (hk : (cpmap cp2).map.Coloring k)
    (hf : ∀ k' : (cpmap (CpStep.H :: cp2)).Dart → Color,
      (cpmap (CpStep.H :: cp2)).map.Coloring k' → CpExtcol et0 cp1 (CpStep.H :: cp2) f k') :
    CpExtcol et0 (CpStep.H :: cp1) cp2 (cpcolor1 .H f) k := by
  have hAB : cpmap (CpStep.R' :: CpStep.K :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)
      = cpmap (CpStep.H :: cp2) := cpmap_expand_H cp2
  have hf' : ∀ k5 : (cpmap (CpStep.R' :: CpStep.K :: CpStep.K :: CpStep.R 1
        :: CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.R' :: CpStep.K :: CpStep.K :: CpStep.R 1
        :: CpStep.U :: cp2)).map.Coloring k5 →
      CpExtcol et0 cp1 (CpStep.R' :: CpStep.K :: CpStep.K :: CpStep.R 1
        :: CpStep.U :: cp2) f k5 := by
    intro k5 hk5
    refine cpExtcol_base_congr et0 cp1 hAB (fun x y hxy => by rw [eq_of_heq hxy])
      (hf k5 (coloring_pmap_congr hAB (fun x y hxy => by rw [eq_of_heq hxy]) hk5))
  have hR' : ∀ k4 : (cpmap (CpStep.K :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).Dart
        → Color,
      (cpmap (CpStep.K :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).map.Coloring k4 →
      CpExtcol et0 (CpStep.R' :: cp1) (CpStep.K :: CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)
        (cpcolor1 .R' f) k4 :=
    fun k4 hk4 => cpcolor1R'_correct et0 hk4 (hf' k4 hk4)
  have hK2 : ∀ k3 : (cpmap (CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)).map.Coloring k3 →
      CpExtcol et0 (CpStep.K :: CpStep.R' :: cp1) (CpStep.K :: CpStep.R 1 :: CpStep.U :: cp2)
        (cpcolor1 .K (cpcolor1 .R' f)) k3 :=
    fun k3 hk3 => cpcolor1K_correct et0 hk3 hR'
  have hK1 : ∀ k2 : (cpmap (CpStep.R 1 :: CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.R 1 :: CpStep.U :: cp2)).map.Coloring k2 →
      CpExtcol et0 (CpStep.K :: CpStep.K :: CpStep.R' :: cp1) (CpStep.R 1 :: CpStep.U :: cp2)
        (cpcolor1 .K (cpcolor1 .K (cpcolor1 .R' f))) k2 :=
    fun k2 hk2 => cpcolor1K_correct et0 hk2 hK2
  have hR1 : ∀ k1 : (cpmap (CpStep.U :: cp2)).Dart → Color,
      (cpmap (CpStep.U :: cp2)).map.Coloring k1 →
      CpExtcol et0 (CpStep.R 1 :: CpStep.K :: CpStep.K :: CpStep.R' :: cp1) (CpStep.U :: cp2)
        (cpcolor1 (.R 1) (cpcolor1 .K (cpcolor1 .K (cpcolor1 .R' f)))) k1 :=
    fun k1 hk1 => cpcolor1R_correct et0 1 (hK1 k1 hk1)
  have hU := cpcolor1U_correct et0 hk hR1
  have h0 : (0 : Color) ∉ trace ((cpmap cp2).cpring.map k) := hk.zero_notMem_trace_cpring _
  exact CpExtcolT.ofT (cpExtcol_head_congr et0 cp1 cp2 hAB
    (fun x => heq_of_eq (injcp_expand_H cp2 x)) (cpcolor1H_expand f h0).symm hU.toT)

/-- **The colouring fold is correct**: for every construction program and every
colouring of the base map, the fold computes the tree of the canonical ring
traces of the colourings extending it. -/
theorem cpcolor1_correct (et0 : List Color) : ∀ (cp1 cp2 : CProg)
    (k : (cpmap cp2).Dart → Color), (cpmap cp2).map.Coloring k →
    CpExtcol et0 cp1 cp2 (List.foldr cpcolor1 cpbranch cp1) k := by
  intro cp1
  induction cp1 with
  | nil => intro cp2 k hk; exact cpbranch_correct et0 hk
  | cons s cp1 ih =>
    intro cp2 k hk
    cases s with
    | R n => exact cpcolor1R_correct et0 n (ih (CpStep.R n :: cp2) k hk)
    | R' => exact cpcolor1R'_correct et0 hk (ih (CpStep.R' :: cp2) k hk)
    | U => exact cpcolor1U_correct et0 hk (ih (CpStep.U :: cp2))
    | K => exact cpcolor1K_correct et0 hk (ih (CpStep.K :: cp2))
    | A => exact cpcolor1A_correct et0 hk (ih (CpStep.A :: cp2))
    | Y => exact cpcolor1Y_correct et0 hk (ih (CpStep.Y :: cp2))
    | H => exact cpcolor1H_correct et0 hk (ih (CpStep.H :: cp2))



/-! ### The base of a construction program

Before the first `U`, `Y` or `H` step a program has built only the single-edge
map, possibly rotated: two darts, each its own face, exchanged by both `edge`
and `node`.  Its colourings are exactly the maps whose two values differ, and
the extra symmetry reductions of `cpcolor0` are justified by recolouring such a
colouring. -/

/-- The base map of a construction program, up to rotation. -/
structure BaseMap (M : PointedMap) : Prop where
  /-- Every face is a single dart. -/
  face : M.map.face = 1
  /-- The node map is an involution. -/
  node_node : ∀ x : M.Dart, M.map.node (M.map.node x) = x
  /-- The edge map is the node map. -/
  edge : ∀ x : M.Dart, M.map.edge x = M.map.node x
  /-- There are only two darts. -/
  two : ∀ x y : M.Dart, y = x ∨ y = M.map.node x
  /-- The two darts are distinct. -/
  node_ne : ∀ x : M.Dart, M.map.node x ≠ x

/-- The node map of the single-edge map. -/
private theorem cpmap0_node (b : Bool) : (cpmap []).map.node b = !b := rfl

/-- The edge map of the single-edge map. -/
private theorem cpmap0_edge (b : Bool) : (cpmap []).map.edge b = !b := rfl

/-- The single-edge map is a base map. -/
theorem baseMap_nil : BaseMap (cpmap []) where
  face := PointedMap.face_cpmap0Map
  node_node x := by
    have h : ∀ b : Bool, (cpmap []).map.node ((cpmap []).map.node b) = b := by
      intro b; rw [cpmap0_node, cpmap0_node, Bool.not_not]
    exact h x
  edge x := by
    have h : ∀ b : Bool, (cpmap []).map.edge b = (cpmap []).map.node b := by
      intro b; rw [cpmap0_node, cpmap0_edge]
    exact h x
  two x y := by
    have h : ∀ b c : Bool, c = b ∨ c = (cpmap []).map.node b := by
      intro b c
      rw [cpmap0_node]
      cases b <;> cases c <;> simp
    exact h x y
  node_ne x := by
    have h : ∀ b : Bool, (cpmap []).map.node b ≠ b := by
      intro b
      rw [cpmap0_node]
      cases b <;> exact fun hc => Bool.noConfusion hc
    exact h x

namespace BaseMap

variable {M : PointedMap}

/-- Rotating the reference dart keeps a base map a base map. -/
theorem ecpR (h : BaseMap M) (n : ℕ) : BaseMap (M.ecpR n) where
  face := h.face
  node_node := h.node_node
  edge := h.edge
  two := h.two
  node_ne := h.node_ne

/-- In a base map two darts share a face only if they are equal. -/
theorem cface_iff (h : BaseMap M) {x y : M.Dart} : M.map.CFace x y ↔ x = y := by
  have hs : M.map.CFace x y ↔ M.map.face.SameCycle x y := Iff.rfl
  rw [hs, h.face]
  constructor
  · rintro ⟨i, hi⟩
    simpa using hi
  · rintro rfl
    exact Equiv.Perm.SameCycle.refl _ _

/-- The ring of a base map is nontrivial. -/
theorem properCpring (h : BaseMap M) : M.map.ProperCpring M.point :=
  (h.node_ne M.point).symm

/-- The ring of a base map has exactly two darts. -/
theorem cpring_eq (h : BaseMap M) :
    M.map.cpring M.point = [M.map.node M.point, M.point] := by
  obtain ⟨d, hdd⟩ : ∃ d, (M.map.cpring M.point).drop 2 = d := ⟨_, rfl⟩
  have hd : M.map.cpring M.point = M.map.node M.point :: M.point :: d := by
    rw [← hdd]; exact Hypermap.head_proper_cpring h.properCpring
  have hnd : (M.map.cpring M.point).Nodup := Hypermap.nodup_cpring
  rw [hd] at hnd
  cases d with
  | nil => rw [hd]
  | cons z t =>
    exfalso
    rcases h.two M.point z with hz | hz
    · exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by rw [hz]; simp)
    · exact (List.nodup_cons.mp hnd).1 (by rw [hz]; simp)

/-- A map with constant trace `c1` on a base map is a colouring. -/
theorem coloring (h : BaseMap M) {k : M.Dart → Color}
    (hk : ∀ x, k (M.map.node x) + k x = c1) : M.map.Coloring k where
  edge x := by
    rw [h.edge]
    intro hc
    have h1 := hk x
    rw [hc, add_self] at h1
    exact absurd h1 (by decide)
  face x := by
    have h1 : M.map.face x = x := by rw [h.face]; rfl
    rw [h1]

/-- The ring trace of such a colouring is `[c1, c1]`. -/
theorem trace_eq (h : BaseMap M) {k : M.Dart → Color}
    (hk : ∀ x, k (M.map.node x) + k x = c1) : trace (M.cpring.map k) = [c1, c1] := by
  rw [show M.cpring = [M.map.node M.point, M.point] from h.cpring_eq, List.map_cons,
    List.map_cons, List.map_nil, trace_cons]
  have h1 : k (M.map.node M.point) + k M.point = c1 := hk M.point
  have h2 : k M.point + k (M.map.node M.point) = c1 := by rw [add_comm]; exact h1
  simp only [List.nil_append, List.cons_append, pairmap_cons, pairmap_nil, h1, h2]

end BaseMap



/-! ### The extra colourings of `cpcolor0`

The first `U` or `Y` step of a program is applied to the single-edge map, whose
colourings are all equivalent up to recolouring.  It is therefore enough to
enumerate three ring traces for a `Y` step, and two for a `U` step. -/

/-- The ring of a `U` extension of a hypermap, as a list of colours. -/
private theorem map_cpring_ecpU_aux {D : Type*} [Finite D] [DecidableEq D]
    (G : Hypermap D) (x₀ : D) (g : EcpDart D → Color) :
    (((G.ecpUMap x₀).cpring .X).map g)
      = g .Xe :: g .X :: (G.cpring x₀).map (fun x => g (.icp x)) := by
  rw [Hypermap.cpring_ecpU, List.map_cons, List.map_cons, List.map_map]
  rfl

/-- The ring of a `U` extension, as a list of colours. -/
theorem map_cpring_ecpU (M : PointedMap) (g : M.ecpU.Dart → Color) :
    M.ecpU.cpring.map g = g .Xe :: g .X :: M.cpring.map (fun x => g (M.icpU x)) :=
  map_cpring_ecpU_aux M.map M.point g

/-- The new face of a `U` step. -/
theorem cface_ecpU_pm (M : PointedMap) (u : M.ecpU.Dart) :
    M.ecpU.map.CFace .X u ↔ u = .X := Hypermap.cface_ecpU M.map M.point u

/-- A `U` step does not change face orbits. -/
theorem cface_icpU_pm (M : PointedMap) (x y : M.Dart) :
    M.ecpU.map.CFace (M.icpU x) (M.icpU y) ↔ M.map.CFace x y :=
  Hypermap.cface_icpU M.map M.point x y

/-- The face of the second new dart of a `U` step. -/
theorem cface_Xe_icpU_pm (M : PointedMap) (z : M.Dart) :
    M.ecpU.map.CFace .Xe (M.icpU z) ↔ M.map.CFace z (M.map.node M.point) :=
  Hypermap.cface_Xe_icpU M.map M.point z

/-- The faces of a `U` step. -/
theorem fband_icpU_pm (M : PointedMap) (u : M.ecpU.Dart) :
    (∃ x : M.Dart, M.ecpU.map.CFace u (M.icpU x)) ∨ M.ecpU.map.CFace .X u :=
  Hypermap.fband_icpU M.map M.point u

/-- The face band of a single dart is its face. -/
theorem fband_singleton_iff {D : Type*} (G : Hypermap D) (y u : D) :
    G.Fband [y] u ↔ G.CFace u y := by
  simp [Hypermap.Fband]

/-- The new face of a `U` step is adjacent exactly to the face of `node x₀`. -/
theorem adj_ecpU_pm (M : PointedMap) (u : M.ecpU.Dart) :
    M.ecpU.map.Adj .X u ↔ M.ecpU.map.CFace u (M.icpU (M.map.node M.point)) :=
  (Hypermap.adj_ecpU M.map M.point u).trans (fband_singleton_iff _ _ _)

open scoped Classical in
/-- The colouring of a `U` extension of the base map with trace `[c1, c1, e, e]`. -/
noncomputable def kU0 (M : PointedMap) (e : Color) : M.ecpU.Dart → Color := fun u =>
  if M.ecpU.map.CFace .X u then c1
  else if M.ecpU.map.CFace u (M.icpU M.point) then e else c0

open scoped Classical in
/-- The colouring of a `Y` extension of the base map with trace `[c1, c2, c3]`. -/
noncomputable def kY0 (M : PointedMap) : M.ecpY.Dart → Color := fun u =>
  if M.ecpY.map.CFace .X u then c2
  else if M.ecpY.map.CFace u (M.icpY M.point) then c0 else c3



namespace BaseMap

variable {M : PointedMap}

/-! #### The `U` colouring -/

/-- `kU0` is constant on faces. -/
theorem kU0_cface (e : Color) {u v : M.ecpU.Dart} (huv : M.ecpU.map.CFace u v) :
    kU0 M e u = kU0 M e v := by
  have h1 : M.ecpU.map.CFace .X u ↔ M.ecpU.map.CFace .X v :=
    ⟨fun hc => hc.trans huv, fun hc => hc.trans huv.symm⟩
  have h2 : M.ecpU.map.CFace u (M.icpU M.point) ↔ M.ecpU.map.CFace v (M.icpU M.point) :=
    ⟨fun hc => huv.symm.trans hc, fun hc => huv.trans hc⟩
  unfold kU0
  by_cases hx : M.ecpU.map.CFace .X u
  · rw [ite_eq_left hx, ite_eq_left (h1.mp hx)]
  · rw [ite_eq_right hx, ite_eq_right (fun hc => hx (h1.mpr hc))]
    by_cases hy : M.ecpU.map.CFace u (M.icpU M.point)
    · rw [ite_eq_left hy, ite_eq_left (h2.mp hy)]
    · rw [ite_eq_right hy, ite_eq_right (fun hc => hy (h2.mpr hc))]

/-- `kU0` on the new dart. -/
@[simp] theorem kU0_X (e : Color) : kU0 M e .X = c1 := by
  have h0 : M.ecpU.map.CFace (.X : M.ecpU.Dart) .X := Equiv.Perm.SameCycle.refl _ _
  unfold kU0
  rw [ite_eq_left h0]

/-- `kU0` is `c1` on the new face. -/
theorem kU0_eq_c1 (e : Color) {u : M.ecpU.Dart} (hu : M.ecpU.map.CFace .X u) :
    kU0 M e u = c1 := (kU0_cface e hu).symm.trans (kU0_X e)

/-- `kU0` on the base point. -/
theorem kU0_icpU_point (e : Color) : kU0 M e (M.icpU M.point) = e := by
  have h1 : ¬ M.ecpU.map.CFace .X (M.icpU M.point) := by
    intro hc
    exact absurd ((cface_ecpU_pm M _).mp hc) (by simp [PointedMap.icpU])
  unfold kU0
  rw [ite_eq_right h1, ite_eq_left (Equiv.Perm.SameCycle.refl _ _)]

/-- `kU0` on the other ring dart. -/
theorem kU0_icpU_node (h : BaseMap M) (e : Color) :
    kU0 M e (M.icpU (M.map.node M.point)) = c0 := by
  have h1 : ¬ M.ecpU.map.CFace .X (M.icpU (M.map.node M.point)) := by
    intro hc
    exact absurd ((cface_ecpU_pm M _).mp hc) (by simp [PointedMap.icpU])
  have h2 : ¬ M.ecpU.map.CFace (M.icpU (M.map.node M.point)) (M.icpU M.point) := by
    intro hc
    exact h.node_ne M.point (h.cface_iff.mp ((cface_icpU_pm M _ _).mp hc))
  unfold kU0
  rw [ite_eq_right h1, ite_eq_right h2]

/-- `kU0` on the second new dart. -/
theorem kU0_Xe (h : BaseMap M) (e : Color) : kU0 M e .Xe = c0 := by
  have h1 : ¬ M.ecpU.map.CFace (.X : M.ecpU.Dart) .Xe := by
    intro hc
    exact absurd ((cface_ecpU_pm M _).mp hc) (by simp)
  have h2 : ¬ M.ecpU.map.CFace (.Xe : M.ecpU.Dart) (M.icpU M.point) := by
    intro hc
    exact h.node_ne M.point (h.cface_iff.mp ((cface_Xe_icpU_pm M _).mp hc)).symm
  unfold kU0
  rw [ite_eq_right h1, ite_eq_right h2]

/-- `kU0` is a colouring for a nonzero offset. -/
theorem kU0_coloring (h : BaseMap M) {e : Color} (he : e ≠ 0) :
    M.ecpU.map.Coloring (kU0 M e) where
  face u := kU0_cface e (M.ecpU.map.cface_face u).symm
  edge u := by
    cases u with
    | X =>
      change kU0 M e .Xe ≠ kU0 M e .X
      rw [h.kU0_Xe, kU0_X]
      decide
    | Xe =>
      change kU0 M e .X ≠ kU0 M e .Xe
      rw [h.kU0_Xe, kU0_X]
      decide
    | icp x =>
      change kU0 M e (M.icpU (M.map.edge x)) ≠ kU0 M e (M.icpU x)
      rw [h.edge x]
      rcases h.two M.point x with hx | hx
      · rw [hx, kU0_icpU_point, h.kU0_icpU_node]
        exact fun hc => he hc.symm
      · rw [hx, h.node_node, kU0_icpU_point, h.kU0_icpU_node]
        exact he

/-- The ring trace of the `U` colouring. -/
theorem trace_kU0 (h : BaseMap M) (e : Color) :
    trace (M.ecpU.cpring.map (kU0 M e)) = [c1, c1, e, e] := by
  rw [map_cpring_ecpU M (kU0 M e),
    show M.cpring = [M.map.node M.point, M.point] from h.cpring_eq,
    List.map_cons, List.map_cons, List.map_nil, h.kU0_Xe, kU0_X, h.kU0_icpU_node,
    kU0_icpU_point, trace_cons]
  simp

/-! #### The `Y` colouring -/

/-- `kY0` is constant on faces. -/
theorem kY0_cface {u v : M.ecpY.Dart} (huv : M.ecpY.map.CFace u v) : kY0 M u = kY0 M v := by
  have h1 : M.ecpY.map.CFace .X u ↔ M.ecpY.map.CFace .X v :=
    ⟨fun hc => hc.trans huv, fun hc => hc.trans huv.symm⟩
  have h2 : M.ecpY.map.CFace u (M.icpY M.point) ↔ M.ecpY.map.CFace v (M.icpY M.point) :=
    ⟨fun hc => huv.symm.trans hc, fun hc => huv.trans hc⟩
  unfold kY0
  by_cases hx : M.ecpY.map.CFace .X u
  · rw [ite_eq_left hx, ite_eq_left (h1.mp hx)]
  · rw [ite_eq_right hx, ite_eq_right (fun hc => hx (h1.mpr hc))]
    by_cases hy : M.ecpY.map.CFace u (M.icpY M.point)
    · rw [ite_eq_left hy, ite_eq_left (h2.mp hy)]
    · rw [ite_eq_right hy, ite_eq_right (fun hc => hy (h2.mpr hc))]

/-- `kY0` is `c2` exactly on the new face. -/
theorem kY0_eq_c2 {u : M.ecpY.Dart} (hu : M.ecpY.map.CFace .X u) : kY0 M u = c2 := by
  unfold kY0
  rw [ite_eq_left hu]

/-- `kY0` is not `c2` away from the new face. -/
theorem kY0_ne_c2 {u : M.ecpY.Dart} (hu : ¬ M.ecpY.map.CFace .X u) : kY0 M u ≠ c2 := by
  unfold kY0
  rw [ite_eq_right hu]
  by_cases hy : M.ecpY.map.CFace u (M.icpY M.point)
  · rw [ite_eq_left hy]; decide
  · rw [ite_eq_right hy]; decide

/-- `kY0` on the base point. -/
theorem kY0_icpY_point : kY0 M (M.icpY M.point) = c0 := by
  unfold kY0
  rw [ite_eq_right (PointedMap.not_cface_ecpY_icpY M M.point),
    ite_eq_left (Equiv.Perm.SameCycle.refl _ _)]

/-- `kY0` on the other ring dart. -/
theorem kY0_icpY_node (h : BaseMap M) : kY0 M (M.icpY (M.map.node M.point)) = c3 := by
  have h2 : ¬ M.ecpY.map.CFace (M.icpY (M.map.node M.point)) (M.icpY M.point) := by
    intro hc
    exact h.node_ne M.point (h.cface_iff.mp ((PointedMap.cface_icpY' M _ _).mp hc))
  unfold kY0
  rw [ite_eq_right (PointedMap.not_cface_ecpY_icpY M _), ite_eq_right h2]

/-- `kY0` on the node of the new dart. -/
theorem kY0_node_X (h : BaseMap M) : kY0 M (M.ecpY.map.node .X) = c3 := by
  rw [kY0_cface (PointedMap.cface_node_ecpY' M), h.kY0_icpY_node]

/-- `kY0` is a colouring. -/
theorem kY0_coloring (h : BaseMap M) : M.ecpY.map.Coloring (kY0 M) where
  face u := kY0_cface (M.ecpY.map.cface_face u).symm
  edge u := by
    have hXX : M.ecpY.map.CFace (.X : M.ecpY.Dart) (.icp .X) :=
      (PointedMap.cface_ecpY M _).mpr (Or.inr rfl)
    have hXXe : ¬ M.ecpY.map.CFace (.X : M.ecpY.Dart) (.icp .Xe) := by
      intro hc
      rcases (PointedMap.cface_ecpY M _).mp hc with h1 | h1
      · exact absurd h1 (by simp)
      · exact absurd (EcpDart.icp_injective h1) (by simp)
    have hXe : ¬ M.ecpY.map.CFace (.X : M.ecpY.Dart) .Xe := by
      intro hc
      rcases (PointedMap.cface_ecpY M _).mp hc with h1 | h1
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
    cases u with
    | X =>
      change kY0 M .Xe ≠ kY0 M .X
      rw [kY0_eq_c2 (Equiv.Perm.SameCycle.refl _ _)]
      exact kY0_ne_c2 hXe
    | Xe =>
      change kY0 M .X ≠ kY0 M .Xe
      rw [kY0_eq_c2 (Equiv.Perm.SameCycle.refl _ _)]
      exact fun hc => kY0_ne_c2 hXe hc.symm
    | icp v =>
      cases v with
      | X =>
        change kY0 M (.icp .Xe) ≠ kY0 M (.icp .X)
        rw [kY0_eq_c2 hXX]
        exact kY0_ne_c2 hXXe
      | Xe =>
        change kY0 M (.icp .X) ≠ kY0 M (.icp .Xe)
        rw [kY0_eq_c2 hXX]
        exact fun hc => kY0_ne_c2 hXXe hc.symm
      | icp x =>
        change kY0 M (M.icpY (M.map.edge x)) ≠ kY0 M (M.icpY x)
        rw [h.edge x]
        rcases h.two M.point x with hx | hx
        · rw [hx, kY0_icpY_point, h.kY0_icpY_node]
          decide
        · rw [hx, h.node_node, kY0_icpY_point, h.kY0_icpY_node]
          decide

end BaseMap



/-- The ring of a `Y` extension, as a list of colours. -/
theorem map_cpring_ecpY (M : PointedMap) (g : M.ecpY.Dart → Color) :
    M.ecpY.cpring.map g
      = g (M.ecpY.map.node .X) :: g .X :: (M.cpring.tail.map M.icpY).map g :=
  congrArg (fun l : List M.ecpY.Dart => l.map g) (PointedMap.cpring_ecpY' M)

namespace BaseMap

variable {M : PointedMap}

/-- The `Y` colouring on the new dart. -/
theorem kY0_X : kY0 M .X = c2 :=
  kY0_eq_c2 (show M.ecpY.map.CFace (.X : M.ecpY.Dart) .X from Equiv.Perm.SameCycle.refl _ _)

/-- The ring trace of the `Y` colouring. -/
theorem trace_kY0 (h : BaseMap M) : trace (M.ecpY.cpring.map (kY0 M)) = [c1, c2, c3] := by
  have htail : M.cpring.tail = [M.point] := by
    rw [show M.cpring = [M.map.node M.point, M.point] from h.cpring_eq]; rfl
  rw [map_cpring_ecpY M (kY0 M), htail]
  simp only [List.map_cons, List.map_nil]
  rw [h.kY0_node_X, kY0_X, kY0_icpY_point, trace_cons]
  decide

end BaseMap



/-- **The `Y` case of `cpcolor0`**: for the first `Y` step of a program three
ring traces suffice, because the base map has only one colouring up to
recolouring. -/
theorem cpcolor0Y_correct (et0 : List Color) (cp' cp2 : CProg) (hb : BaseMap (cpmap cp2))
    {k : (cpmap cp2).Dart → Color}
    (hk : ∀ x, k ((cpmap cp2).map.node x) + k x = c1) :
    CpExtcol et0 (CpStep.Y :: cp') cp2
      (fun _ => List.foldr cpcolor1 cpbranch cp' [c1, c2, c3]) k := by
  have hcol' : (cpmap (CpStep.Y :: cp2)).map.Coloring (kY0 (cpmap cp2)) := hb.kY0_coloring
  have h := cpcolor1_correct et0 cp' (CpStep.Y :: cp2) (kY0 (cpmap cp2)) hcol'
  have htr : trace ((cpmap (CpStep.Y :: cp2)).cpring.map (kY0 (cpmap cp2))) = [c1, c2, c3] :=
    hb.trace_kY0
  have hp : Ctree.Proper (cpHeight (cp'.reverseAux (CpStep.Y :: cp2)))
      (List.foldr cpcolor1 cpbranch cp'
        (trace ((cpmap (CpStep.Y :: cp2)).cpring.map (kY0 (cpmap cp2))))) := h.proper
  have hm : Ctree.mem (List.foldr cpcolor1 cpbranch cp'
        (trace ((cpmap (CpStep.Y :: cp2)).cpring.map (kY0 (cpmap cp2)))))
        (normTail et0) = true ↔
      ∃ k0 : (cpmap (cp'.reverseAux (CpStep.Y :: cp2))).Dart → Color,
        (cpmap (cp'.reverseAux (CpStep.Y :: cp2))).map.Coloring k0 ∧
          CpTrace0 et0 (cp'.reverseAux (CpStep.Y :: cp2)) k0 ∧
          ∀ u, k0 (injcp cp' (CpStep.Y :: cp2) u) = kY0 (cpmap cp2) u := h.mem
  rw [htr] at hp hm
  have hnp : k ((cpmap cp2).map.node (cpmap cp2).point) = k (cpmap cp2).point + c1 := by
    have h1 := hk (cpmap cp2).point
    rw [← h1, add_comm (k ((cpmap cp2).map.node (cpmap cp2).point)), ← add_assoc,
      add_self, zero_add]
  have hsum : k (cpmap cp2).point + k ((cpmap cp2).map.node (cpmap cp2).point) = c1 := by
    rw [hnp, ← add_assoc, add_self, zero_add]
  refine ⟨hp, hm.trans ?_⟩
  constructor
  · rintro ⟨k0, hk0, ht0, hkk⟩
    obtain ⟨hc, ht⟩ := CpTrace0.perm hk0 ht0 (k (cpmap cp2).point) e231
    refine ⟨_, hc, ht, ?_⟩
    intro x
    change k (cpmap cp2).point + e231 (k0 (injcp cp' (CpStep.Y :: cp2)
      ((cpmap cp2).icpY x))) = k x
    rw [hkk ((cpmap cp2).icpY x)]
    rcases hb.two (cpmap cp2).point x with hx | hx
    · rw [hx, BaseMap.kY0_icpY_point]
      change k (cpmap cp2).point + c0 = k (cpmap cp2).point
      rw [Color.c0_eq_zero, add_zero]
    · rw [hx, hb.kY0_icpY_node, hnp]
      rfl
  · rintro ⟨k0, hk0, ht0, hkk⟩
    obtain ⟨e0, he0⟩ : ∃ e0, k (cpmap cp2).point
        + k0 (injcp cp' (CpStep.Y :: cp2) .X) = e0 := ⟨_, rfl⟩
    have hproper : (cpmap cp2).Proper := hb.properCpring
    have hkp : k0 (injcp cp' (CpStep.Y :: cp2) ((cpmap cp2).icpY (cpmap cp2).point))
        = k (cpmap cp2).point := hkk (cpmap cp2).point
    have hkn : k0 (injcp cp' (CpStep.Y :: cp2)
        ((cpmap cp2).icpY ((cpmap cp2).map.node (cpmap cp2).point)))
        = k ((cpmap cp2).map.node (cpmap cp2).point) :=
      hkk ((cpmap cp2).map.node (cpmap cp2).point)
    have hadjp := adj_injcp_ne (cp1 := cp') (cp2 := CpStep.Y :: cp2) hk0
      ((PointedMap.adj_ecpY (cpmap cp2) hproper _).mpr
        (Or.inr (Equiv.Perm.SameCycle.refl _ _)))
    have hadjn := adj_injcp_ne (cp1 := cp') (cp2 := CpStep.Y :: cp2) hk0
      ((PointedMap.adj_ecpY (cpmap cp2) hproper _).mpr
        (Or.inl (Equiv.Perm.SameCycle.refl _ _)))
    rw [hkp] at hadjp
    rw [hkn] at hadjn
    have hne0 : e0 ≠ 0 := by
      rw [← he0]
      intro hc
      exact hadjp (Color.add_eq_zero_iff.mp hc).symm
    have hne1 : e0 ≠ c1 := by
      rw [← he0]
      intro hc
      refine hadjn ?_
      have h1 : k (cpmap cp2).point
          + (k (cpmap cp2).point + k0 (injcp cp' (CpStep.Y :: cp2) .X))
          = k (cpmap cp2).point + c1 := by rw [hc]
      rw [← add_assoc, add_self, zero_add] at h1
      rw [h1, ← hnp]
    obtain ⟨h0, hh0e, hh0c1⟩ : ∃ h0 : EdgePerm, h0 e0 = c2 ∧ h0 c1 = c3 := by
      cases he : e0 with
      | c0 => exact absurd he hne0
      | c1 => exact absurd he hne1
      | c2 => exact ⟨e321, by decide, by decide⟩
      | c3 => exact ⟨e312, by decide, by decide⟩
    obtain ⟨hc, ht⟩ := CpTrace0.perm hk0 ht0 (h0 (k (cpmap cp2).point)) h0
    refine ⟨_, hc, ht, ?_⟩
    intro u
    rcases PointedMap.fband_icpY' (cpmap cp2) u with ⟨x, hx⟩ | hX
    · rw [cface_injcp_eq (cp1 := cp') (cp2 := CpStep.Y :: cp2) hk0 hx,
        BaseMap.kY0_cface hx]
      rcases hb.two (cpmap cp2).point x with hxx | hxx
      · rw [hxx, hkp, BaseMap.kY0_icpY_point, ← EdgePerm.apply_add, add_self]
        rfl
      · rw [hxx, hkn, hb.kY0_icpY_node, ← EdgePerm.apply_add, hsum, hh0c1]
    · rw [cface_injcp_eq (cp1 := cp') (cp2 := CpStep.Y :: cp2) hk0 hX.symm,
        BaseMap.kY0_eq_c2 hX, ← EdgePerm.apply_add, he0, hh0e]



/-- **The `U` case of `cpcolor0`**: for the first `U` step of a program two ring
traces suffice. -/
theorem cpcolor0U_correct (et0 : List Color) (cp' cp2 : CProg) (hb : BaseMap (cpmap cp2))
    {k : (cpmap cp2).Dart → Color}
    (hk : ∀ x, k ((cpmap cp2).map.node x) + k x = c1) :
    CpExtcol et0 (CpStep.U :: cp') cp2
      (fun _ => Ctree.union (List.foldr cpcolor1 cpbranch cp' [c1, c1, c2, c2])
        (List.foldr cpcolor1 cpbranch cp' [c1, c1, c1, c1])) k := by
  have hpn : k ((cpmap cp2).map.node (cpmap cp2).point) + c1 = k (cpmap cp2).point := by
    have h1 := hk (cpmap cp2).point
    rw [← h1, ← add_assoc, add_self, zero_add]
  have key : ∀ e : Color, e ≠ 0 →
      Ctree.Proper (cpHeight (cp'.reverseAux (CpStep.U :: cp2)))
        (List.foldr cpcolor1 cpbranch cp' [c1, c1, e, e])
      ∧ (Ctree.mem (List.foldr cpcolor1 cpbranch cp' [c1, c1, e, e])
          (normTail et0) = true ↔
          ∃ k0 : (cpmap (cp'.reverseAux (CpStep.U :: cp2))).Dart → Color,
            (cpmap (cp'.reverseAux (CpStep.U :: cp2))).map.Coloring k0 ∧
              CpTrace0 et0 (cp'.reverseAux (CpStep.U :: cp2)) k0 ∧
              ∀ u, k0 (injcp cp' (CpStep.U :: cp2) u) = kU0 (cpmap cp2) e u) := by
    intro e he
    have hcol' : (cpmap (CpStep.U :: cp2)).map.Coloring (kU0 (cpmap cp2) e) :=
      hb.kU0_coloring he
    have h := cpcolor1_correct et0 cp' (CpStep.U :: cp2) (kU0 (cpmap cp2) e) hcol'
    have hp : Ctree.Proper (cpHeight (cp'.reverseAux (CpStep.U :: cp2)))
        (List.foldr cpcolor1 cpbranch cp'
          (trace ((cpmap (CpStep.U :: cp2)).cpring.map (kU0 (cpmap cp2) e)))) := h.proper
    have hm : Ctree.mem (List.foldr cpcolor1 cpbranch cp'
          (trace ((cpmap (CpStep.U :: cp2)).cpring.map (kU0 (cpmap cp2) e))))
          (normTail et0) = true ↔
        ∃ k0 : (cpmap (cp'.reverseAux (CpStep.U :: cp2))).Dart → Color,
          (cpmap (cp'.reverseAux (CpStep.U :: cp2))).map.Coloring k0 ∧
            CpTrace0 et0 (cp'.reverseAux (CpStep.U :: cp2)) k0 ∧
            ∀ u, k0 (injcp cp' (CpStep.U :: cp2) u) = kU0 (cpmap cp2) e u := h.mem
    have htr : trace ((cpmap (CpStep.U :: cp2)).cpring.map (kU0 (cpmap cp2) e))
        = [c1, c1, e, e] := hb.trace_kU0 e
    rw [htr] at hp hm
    exact ⟨hp, hm⟩
  have p2 := (key c2 (by decide)).1
  have p1 := (key c1 (by decide)).1
  refine ⟨Ctree.union_proper _ _ _ p2 p1, ?_⟩
  rw [Ctree.mem_union _ _ _ _ p2 p1]
  constructor
  · intro hmem
    have hone : ∃ (e : Color) (g : EdgePerm), e ≠ 0 ∧ g e = c1 ∧ g 0 = 0 ∧
        Ctree.mem (List.foldr cpcolor1 cpbranch cp' [c1, c1, e, e])
          (normTail et0) = true := by
      rcases Bool.or_eq_true_iff.mp hmem with hme | hme
      · exact ⟨c2, e213, by decide, by decide, by decide, hme⟩
      · exact ⟨c1, 1, by decide, by decide, by decide, hme⟩
    obtain ⟨e, g, he, hge, hg0, hme⟩ := hone
    obtain ⟨k0, hk0, ht0, hkk⟩ := (key e he).2.mp hme
    obtain ⟨hc, ht⟩ := CpTrace0.perm hk0 ht0
      (k ((cpmap cp2).map.node (cpmap cp2).point)) g
    refine ⟨_, hc, ht, ?_⟩
    intro x
    change k ((cpmap cp2).map.node (cpmap cp2).point)
      + g (k0 (injcp cp' (CpStep.U :: cp2) ((cpmap cp2).icpU x))) = k x
    rw [hkk ((cpmap cp2).icpU x)]
    rcases hb.two (cpmap cp2).point x with hx | hx
    · rw [hx, BaseMap.kU0_icpU_point, hge, hpn]
    · rw [hx, hb.kU0_icpU_node, Color.c0_eq_zero, hg0, add_zero]
  · rintro ⟨k0, hk0, ht0, hkk⟩
    obtain ⟨e0, he0⟩ : ∃ e0, k ((cpmap cp2).map.node (cpmap cp2).point)
        + k0 (injcp cp' (CpStep.U :: cp2) .X) = e0 := ⟨_, rfl⟩
    have hkp : k0 (injcp cp' (CpStep.U :: cp2) ((cpmap cp2).icpU (cpmap cp2).point))
        = k (cpmap cp2).point := hkk (cpmap cp2).point
    have hkn : k0 (injcp cp' (CpStep.U :: cp2)
        ((cpmap cp2).icpU ((cpmap cp2).map.node (cpmap cp2).point)))
        = k ((cpmap cp2).map.node (cpmap cp2).point) :=
      hkk ((cpmap cp2).map.node (cpmap cp2).point)
    have hadjn := adj_injcp_ne (cp1 := cp') (cp2 := CpStep.U :: cp2) hk0
      ((adj_ecpU_pm (cpmap cp2) _).mpr (Equiv.Perm.SameCycle.refl _ _))
    rw [hkn] at hadjn
    have hne0 : e0 ≠ 0 := by
      rw [← he0]
      intro hcz
      exact hadjn (Color.add_eq_zero_iff.mp hcz).symm
    have hmain : ∀ (e : Color) (h0 : EdgePerm), h0 e0 = c1 → h0 c1 = e → h0 0 = 0 →
        ∀ u, h0 (k ((cpmap cp2).map.node (cpmap cp2).point)) + h0 (k0
          (injcp cp' (CpStep.U :: cp2) u)) = kU0 (cpmap cp2) e u := by
      intro e h0 hh0e hh0c1 hh00 u
      rcases fband_icpU_pm (cpmap cp2) u with ⟨x, hx⟩ | hX
      · rw [cface_injcp_eq (cp1 := cp') (cp2 := CpStep.U :: cp2) hk0 hx,
          BaseMap.kU0_cface e hx]
        rcases hb.two (cpmap cp2).point x with hxx | hxx
        · rw [hxx, hkp, BaseMap.kU0_icpU_point, ← EdgePerm.apply_add,
            hk (cpmap cp2).point, hh0c1]
        · rw [hxx, hkn, hb.kU0_icpU_node, ← EdgePerm.apply_add, add_self, hh00]
          rfl
      · rw [cface_injcp_eq (cp1 := cp') (cp2 := CpStep.U :: cp2) hk0 hX.symm,
          BaseMap.kU0_eq_c1 e hX, ← EdgePerm.apply_add, he0, hh0e]
    by_cases hc1 : e0 = c1
    · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
      refine (key c1 (by decide)).2.mpr ?_
      obtain ⟨hc, ht⟩ := CpTrace0.perm hk0 ht0
        ((1 : EdgePerm) (k ((cpmap cp2).map.node (cpmap cp2).point))) 1
      exact ⟨_, hc, ht, hmain c1 1 (by rw [hc1]; decide) (by decide) (by decide)⟩
    · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
      refine (key c2 (by decide)).2.mpr ?_
      obtain ⟨h0, hh0e, hh0c1, hh00⟩ :
          ∃ h0 : EdgePerm, h0 e0 = c1 ∧ h0 c1 = c2 ∧ h0 0 = 0 := by
        cases he : e0 with
        | c0 => exact absurd he hne0
        | c1 => exact absurd he hc1
        | c2 => exact ⟨e213, by decide, by decide, by decide⟩
        | c3 => exact ⟨e231, by decide, by decide, by decide⟩
      obtain ⟨hc, ht⟩ := CpTrace0.perm hk0 ht0
        (h0 (k ((cpmap cp2).map.node (cpmap cp2).point))) h0
      exact ⟨_, hc, ht, hmain c2 h0 hh0e hh0c1 hh00⟩



/-! ### The colouring tree of a program -/

/-- Reversing a program twice: the target of the fold started at the empty
program. -/
theorem reverseAux_reverse_nil (cp : CProg) : cp.reverse.reverseAux [] = cp := by
  rw [List.reverseAux_eq, List.reverse_reverse, List.append_nil]

/-- The reference colouring of the single-edge map. -/
noncomputable def kBool : (cpmap []).Dart → Color
  | true => c3
  | false => c2

/-- The reference colouring has all its trace entries equal to `c1`. -/
theorem kBool_spec : ∀ x, kBool ((cpmap []).map.node x) + kBool x = c1 := by
  have h : ∀ b : Bool, kBool ((cpmap []).map.node b) + kBool b = c1 := by
    intro b
    rw [cpmap0_node]
    cases b <;> rfl
  exact h

/-- The default clause of `cpcolor0`. -/
theorem cpcolor0_default (et0 : List Color) {cp cp2 : CProg} (hb : BaseMap (cpmap cp2))
    {k : (cpmap cp2).Dart → Color} (hk : ∀ x, k ((cpmap cp2).map.node x) + k x = c1)
    (hcp : cpcolor0 cp = List.foldr cpcolor1 cpbranch cp [c1, c1]) :
    CpExtcol et0 cp cp2 (fun _ => cpcolor0 cp) k := by
  have hcol := hb.coloring hk
  have h := cpcolor1_correct et0 cp cp2 k hcol
  have hp : Ctree.Proper (cpHeight (cp.reverseAux cp2))
      (List.foldr cpcolor1 cpbranch cp (trace ((cpmap cp2).cpring.map k))) := h.proper
  have hm : Ctree.mem (List.foldr cpcolor1 cpbranch cp
        (trace ((cpmap cp2).cpring.map k))) (normTail et0) = true ↔
      ∃ k0 : (cpmap (cp.reverseAux cp2)).Dart → Color,
        (cpmap (cp.reverseAux cp2)).map.Coloring k0 ∧
          CpTrace0 et0 (cp.reverseAux cp2) k0 ∧
          ∀ x, k0 (injcp cp cp2 x) = k x := h.mem
  rw [hb.trace_eq hk, ← hcp] at hp hm
  exact ⟨hp, hm⟩

/-- **`cpcolor0` is correct**: it computes the tree of the canonical ring traces
of the colourings of the map the program builds on top of a base map. -/
theorem cpcolor0_correct (et0 : List Color) : ∀ (cp cp2 : CProg), BaseMap (cpmap cp2) →
    ∀ k : (cpmap cp2).Dart → Color, (∀ x, k ((cpmap cp2).map.node x) + k x = c1) →
    CpExtcol et0 cp cp2 (fun _ => cpcolor0 cp) k := by
  intro cp
  induction cp with
  | nil => intro cp2 hb k hk; exact cpcolor0_default et0 hb hk rfl
  | cons s cp' ih =>
    intro cp2 hb k hk
    cases s with
    | R n => exact cpcolor1R_correct et0 n (ih (CpStep.R n :: cp2) (hb.ecpR n) k hk)
    | R' => exact cpcolor0_default et0 hb hk rfl
    | K => exact cpcolor0_default et0 hb hk rfl
    | H => exact cpcolor0_default et0 hb hk rfl
    | A => exact cpcolor0_default et0 hb hk rfl
    | Y => exact cpcolor0Y_correct et0 cp' cp2 hb hk
    | U => exact cpcolor0U_correct et0 cp' cp2 hb hk

/-- A tree of height zero is empty or a leaf. -/
theorem Ctree.empty_or_leaf {t : Ctree} (h : Ctree.Proper 0 t) :
    t = .empty ∨ Ctree.isLeaf t = true := by
  cases t with
  | empty => exact Or.inl rfl
  | node _ _ _ => exact absurd h not_false
  | leaf _ => exact Or.inr rfl

/-- The rotation of the empty tree. -/
@[simp] theorem Ctree.consRot_empty : Ctree.consRot .empty = .empty := rfl

/-- **`cpcolor cp` is a proper tree** of the height predicted by the ring size. -/
theorem cpcolor_proper (cp : CProg) : Ctree.Proper (cprsize cp - 1) (cpcolor cp) := by
  have hsize : (cpmap cp).cpring.length = cprsize cp := size_ring_cpmap cp
  have hpos : 0 < cprsize cp := by
    rw [← hsize]; exact Hypermap.length_cpring_pos
  have hh : cpHeight (cp.reverse.reverseAux []) = cprsize cp - 2 := by
    rw [reverseAux_reverse_nil, cpHeight, hsize]
  have h := cpcolor0_correct [] cp.reverse [] baseMap_nil kBool kBool_spec
  have hp : Ctree.Proper (cpHeight (cp.reverse.reverseAux [])) (cpcolor0 cp.reverse) := h.proper
  rw [hh] at hp
  match hn : cprsize cp, hpos with
  | 1, _ =>
    have hempty : cpcolor0 cp.reverse = .empty := by
      rw [hn] at hp
      rcases Ctree.empty_or_leaf hp with hc | hc
      · exact hc
      · exfalso
        have h1 := cpcolor0_correct [c1] cp.reverse [] baseMap_nil kBool kBool_spec
        have hmem : Ctree.mem (cpcolor0 cp.reverse) (normTail [c1]) = true := by
          rw [show normTail [c1] = [] from rfl, Ctree.mem_nil]
          exact hc
        obtain ⟨k0, hk0, -, -⟩ := h1.mem.mp hmem
        have hlt := Hypermap.proper_cpring_iff.mp
          (hk0.properCpring (cpmap (cp.reverse.reverseAux [])).point)
        have hlt2 : 1 < (cpmap (cp.reverse.reverseAux [])).cpring.length := hlt
        rw [show (cpmap (cp.reverse.reverseAux [])).cpring.length
          = cprsize (cp.reverse.reverseAux []) from size_ring_cpmap _,
          reverseAux_reverse_nil, hn] at hlt2
        omega
    rw [cpcolor, hempty]
    exact trivial
  | (m + 2), _ =>
    rw [hn] at hp
    have hm2 : m + 2 - 2 = m := by omega
    rw [hm2] at hp
    have hm1 : m + 2 - 1 = m + 1 := by omega
    rw [hm1, cpcolor]
    exact Ctree.consRot_proper hp



/-- Existential colouring statements transport along an equality of pointed
maps. -/
theorem exists_coloring_pmap_congr {M M' : PointedMap} (hM : M = M') {A : Type*}
    (a : A → M.Dart) (b : A → M'.Dart) (hab : ∀ x, HEq (a x) (b x))
    (t : List Color) (kb : A → Color) :
    (∃ k0 : M.Dart → Color, M.map.Coloring k0 ∧
        t = evenPartialTail ((M.cpring.map k0).rotate 1) ∧ ∀ x, k0 (a x) = kb x)
    ↔ (∃ k0 : M'.Dart → Color, M'.map.Coloring k0 ∧
        t = evenPartialTail ((M'.cpring.map k0).rotate 1) ∧ ∀ x, k0 (b x) = kb x) := by
  subst hM
  have hh : a = b := funext fun x => eq_of_heq (hab x)
  subst hh
  exact Iff.rfl

/-- Adjacency transports along an equality of pointed maps. -/
theorem adj_pmap_congr {M M' : PointedMap} (hM : M = M') {x y : M.Dart} {x' y' : M'.Dart}
    (hx : HEq x x') (hy : HEq y y') (h : M.map.Adj x y) : M'.map.Adj x' y' := by
  subst hM
  rw [← eq_of_heq hx, ← eq_of_heq hy]
  exact h

/-- **The specification of `cpcolor`**: the tree `cpcolor cp` holds exactly the
even traces `et` whose completion is the ring trace of a colouring of the map
built by `cp`. -/
theorem ctree_mem_cpcolor (cp : CProg) (et : List Color) :
    Ctree.mem (cpcolor cp) et = true ↔
      evenTrace et = true ∧
        (cpmap cp).map.RingTrace (cpmap cp).cpring (et.sum :: et) := by
  have hM : cpmap (cp.reverse.reverseAux []) = cpmap cp :=
    congrArg cpmap (reverseAux_reverse_nil cp)
  have hD : (cpmap (cp.reverse.reverseAux [])).Dart = (cpmap cp).Dart :=
    congrArg PointedMap.Dart hM
  obtain ⟨b, hb⟩ : ∃ b : (cpmap []).Dart → (cpmap cp).Dart,
      ∀ x, HEq (injcp cp.reverse [] x) (b x) :=
    ⟨fun x => cast hD (injcp cp.reverse [] x), fun x => (cast_heq hD _).symm⟩
  have hadj : (cpmap cp).map.Adj (b false) (b true) :=
    adj_pmap_congr hM (hb false) (hb true)
      (sub_adj_injcp cp.reverse [] ((adj_cpmap0 false true).mpr rfl))
  have h := cpcolor0_correct et cp.reverse [] baseMap_nil kBool kBool_spec
  have hm : Ctree.mem (cpcolor0 cp.reverse) (normTail et) = true ↔
      ∃ k0 : (cpmap (cp.reverse.reverseAux [])).Dart → Color,
        (cpmap (cp.reverse.reverseAux [])).map.Coloring k0 ∧
          normTail et
            = evenPartialTail (((cpmap (cp.reverse.reverseAux [])).cpring.map k0).rotate 1) ∧
          ∀ x, k0 (injcp cp.reverse [] x) = kBool x := h.mem
  rw [exists_coloring_pmap_congr hM (injcp cp.reverse []) b hb (normTail et) kBool] at hm
  rw [cpcolor, Ctree.mem_consRot, hm]
  constructor
  · rintro ⟨k0, hk0, htr0, -⟩
    have hpt : evenPartialTail (((cpmap cp).cpring.map k0).rotate 1)
        = evenNormTail (trace ((cpmap cp).cpring.map k0)).tail := by
      rw [evenPartialTail, ← tail_trace]
    rw [hpt] at htr0
    have h0u : (0 : Color) ∉ trace ((cpmap cp).cpring.map k0) :=
      hk0.zero_notMem_trace_cpring _
    have hputail : ProperTrace (trace ((cpmap cp).cpring.map k0)).tail :=
      hk0.properTrace_tail_trace_cpring _
    have hnz : (0 : Color) ∉ evenNormTail (trace ((cpmap cp).cpring.map k0)).tail := by
      simp only [evenNormTail, mem_zero_map, mem_zero_normTail, not_or, not_not]
      exact ⟨hputail, fun hc => h0u (List.mem_of_mem_tail hc)⟩
    have hnzet : (0 : Color) ∉ normTail et := by rw [htr0]; exact hnz
    have hpet : ProperTrace et := by
      by_contra hc
      exact hnzet (mem_zero_normTail.mpr (Or.inl hc))
    have heven : evenTrace et = true := by
      rw [evenTrace, htr0]
      exact evenTail_evenNormTail _
    have hen : evenNormTail et = evenNormTail (trace ((cpmap cp).cpring.map k0)).tail := by
      rw [evenNormTail, evenPerm, ite_eq_left heven, map_one_edgePerm]
      exact htr0
    obtain ⟨g1, hg1⟩ := exists_map_eq_cons_evenNormTail hpet
    obtain ⟨g2, hg2⟩ := exists_map_eq_cons_evenNormTail hputail
    obtain ⟨g, hgdef⟩ : ∃ g : EdgePerm, g1⁻¹ * g2 = g := ⟨_, rfl⟩
    have hkey : (trace ((cpmap cp).cpring.map k0)).tail.map g = et := by
      rw [← hgdef, ← map_map_edgePerm, hg2, ← hen, ← hg1, map_map_edgePerm,
        inv_mul_cancel, map_one_edgePerm]
    have hune : trace ((cpmap cp).cpring.map k0) ≠ [] := by
      intro hc
      have hl := congrArg List.length hc
      rw [length_trace, List.length_map, List.length_nil] at hl
      exact absurd hl (Nat.ne_of_gt Hypermap.length_cpring_pos)
    obtain ⟨a, ut, hu⟩ := List.exists_cons_of_ne_nil hune
    have hsum0 : a + ut.sum = 0 := by
      have h1 : (trace ((cpmap cp).cpring.map k0)).sum = 0 := sum_trace _
      rw [hu, List.sum_cons] at h1
      exact h1
    have hga : g a = et.sum := by
      rw [show a = ut.sum from Color.add_eq_zero_iff.mp hsum0, ← hkey, hu, List.tail_cons,
        map_sum]
    refine ⟨heven, ⟨(g : Color → Color) ∘ k0, hk0.comp (EdgePerm.apply_injective g), ?_⟩⟩
    rw [← List.map_map, trace_map, hu, List.map_cons, hga]
    rw [hu, List.tail_cons] at hkey
    rw [hkey]
  · rintro ⟨heven, k, hk, htr⟩
    have hne : k (b false) ≠ k (b true) := hk.ne_of_adj hadj
    obtain ⟨e0, he0⟩ : ∃ e0, k (b false) + k (b true) = e0 := ⟨_, rfl⟩
    have he0ne : e0 ≠ 0 := by
      rw [← he0]
      intro hc
      exact hne (Color.add_eq_zero_iff.mp hc)
    have hh0 : (rotTo e0) e0 = c1 := rotTo_apply_self he0ne
    obtain ⟨c, hc⟩ : ∃ c, c2 + (rotTo e0) (k (b false)) = c := ⟨_, rfl⟩
    have hinj : Function.Injective (fun d : Color => c + (rotTo e0) d) := by
      intro d₁ d₂ hd
      exact EdgePerm.apply_injective _ (by simpa using hd)
    refine ⟨fun w => c + (rotTo e0) (k w),
      hk.comp (h := fun d : Color => c + (rotTo e0) d) hinj, ?_, ?_⟩
    · rw [evenPartialTail, ← tail_trace]
      have hmapk : (cpmap cp).cpring.map (fun w => c + (rotTo e0) (k w))
          = (((cpmap cp).cpring.map k).map (rotTo e0 : Color → Color)).map (fun d => c + d) := by
        rw [List.map_map, List.map_map]
        rfl
      rw [hmapk, trace_map_add, trace_map, ← htr, List.map_cons, List.tail_cons,
        evenNormTail_map, evenNormTail, evenPerm, ite_eq_left heven, map_one_edgePerm]
    · intro x
      cases x with
      | false =>
        change c + (rotTo e0) (k (b false)) = kBool false
        rw [← hc, add_assoc, add_self, add_zero]
        rfl
      | true =>
        change c + (rotTo e0) (k (b true)) = kBool true
        rw [← hc, add_assoc, ← EdgePerm.apply_add, he0, hh0]
        rfl


end FourColor

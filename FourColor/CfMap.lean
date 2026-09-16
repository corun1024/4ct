import FourColor.Geometry
import FourColor.Coloring
import FourColor.Orbit

/-!
# Configuration maps

Configuration maps are entered as little linear construction programs: starting
from a single edge, these build a sequence of concentric quasicubic maps,
alternately rotating the perimeter and adding one or two outer nodes (and with
them a new region).

The reference presents each construction step as an explicit triple of dart
maps together with a `cancel3` identity.  Here a hypermap is a triple of
`Equiv.Perm`s, so `Hypermap.ofCancel3` turns such a triple into a hypermap: on a
finite dart type the identity `node (face (edge x)) = x` already forces all
three maps to be permutations.  The ring of a pointed map is the orbit list of
`node⁻¹`, and it is computed for each step from `Hypermap.cpring_eq`, the
statement that the ring is the *only* duplicate-free reverse N-cycle starting at
`node x₀`.

Two small divergences from the reference: an `R n` step rotates the ring by
`n` modulo its size rather than being the identity when `n` overflows (the two
agree for every `n` below the ring size, which is all the construction programs
use), and `ConfigProg` is stated as "every step is an `R`, `Y` or `H` step, and
the last step is a `Y` step" rather than by the reference's recursion.

## Main definitions

* `CpStep`, `CProg`, `Config` — construction steps, programs and configuration
  records, with the `CubicProg` and `ConfigProg` well-formedness predicates.
* `Hypermap.cpring` — the ring (reverse N-cycle) of a pointed hypermap, with
  `Hypermap.ProperCpring` and `Hypermap.LongCpring`.
* `EcpDart` — a dart type extended with the two darts of a new edge; and
  `Hypermap.ofCancel3`, building a hypermap from three dart maps.
* `PointedMap`, and the step constructions `PointedMap.ecpR`, `ecpA`, `ecpU`,
  `ecpN`, `ecpR'`, `ecpK`, `ecpY`, `ecpH`.
* `cpmap`, `cfmap`, `cfring`, `cprsize`, `cpksize`, `cpker` — running a program,
  and the sizes of the resulting ring and kernel.
* `injcp` — the injection of the darts of `cpmap cp2` into `cpmap (cp1 ++ cp2)`
  read right to left.
* `CfMask`, `cpmask`, `cfmask1` — bit masks selecting faces of a configuration
  map.

## Main results

* `eq_orbitList_of_isCyclicChain`, `Hypermap.cpring_eq` — a duplicate-free
  cyclic chain is the orbit list of its head, so the ring is determined by its
  first dart.
* `Hypermap.cpring_ecpR`, `cpring_ecpU`, `cpring_ecpN_of_long`,
  `cpring_ecpN_of_not_long` — the rings of the basic steps, and
  `PointedMap.length_cpring_ecpY`, `length_cpring_ecpH`, `length_cpring_ecpK`
  for the composite ones.
* `Hypermap.plain_ecpU`, `plain_ecpN`, `quasicubic_ecpR`, `quasicubic_ecpU`,
  `quasicubic_ecpN_of_long` — the geometry of the basic steps.
* `cpmap_proper`, `cfmap_long`, `cpmap_plain`, `cpmap_cubic`,
  `size_ring_cpmap` — the geometry of the map of a program.
* `injcp_injective`, `edge_injcp` — the dart injections are injective and
  commute with `edge`.
* `Hypermap.cface_ecpU`, `cface_icpU`, `cface_icpN`, `cface_ecpN`,
  `PointedMap.cface_icpY`, `cface_icpH`, `cface_icpK`, `Hypermap.cface_icpA` —
  the face orbits of the construction steps, computed from the description of
  each face map as the face map of the base map composed with transpositions
  (`sameCycle_swap_mul`).
* `Hypermap.adj_ecpU`, `adj_icpU`, `adj_icpN`, `PointedMap.adj_icpY`,
  `adj_icpH`, `adj_icpK`, `Hypermap.sub_adj_icpA` — the adjacency of the steps,
  and `fband_icpU`, `fband_icpN`, `PointedMap.fband_icpY`, `fband_icpH`,
  `fband_icpK` for the faces they cover.
* `Hypermap.connected_ecpU`, `connected_ecpN`, `planar_ecpU`, `planar_ecpN`,
  `bridgeless_ecpU`, `bridgeless_ecpN`, and `cpmap_connected`,
  `cpmap_bridgeless`, `cpmap_planar`.
* `Hypermap.cpring_ecpA_of_long`, `length_cpring_ecpA`, `cpring_ecpK` — the
  rings of the merge and inverted-Y steps, and `size_ring_cpmap`, which now
  holds for every program.
* `cface_injcp`, `adj_injcp`, `node_injcp`, `cnode_injcp`, `sub_cface_injcp`,
  `sub_adj_injcp` — the dart injections and the three orbit relations.
* `cpexpand`, `cpmap_cpexpand` — replacing every `Y` and `H` step by an
  equivalent program of `R`, `R'`, `K` and `U` steps does not change the map.
* `size_cpker`, `cpmask1` — the size of the kernel transversal and the mask
  selecting a single kernel face.
* `PointedMap.adj_ecpY`, `adj_ecpH`, `cpring_ecpY'`, `cpring_ecpH'` — the faces
  adjacent to the new face of a `Y` or `H` step, and the rings of the
  composites.
* `cpmap_simple`, `cpmap_cover` — the perimeter and the kernel transversal of a
  configuration map meet every face exactly once.
* `cpadj`, `cpadj_proper`, `cpmask_adj` — the mask of the faces adjacent to a
  masked set of faces, and its correctness.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/cfmap.v` of the Coq development.
-/

namespace FourColor

open Equiv Equiv.Perm

variable {D D' : Type*}

/-! ### Orbits as cycles

A duplicate-free cyclic chain for a permutation is exactly the orbit list of its
head; this is the reference's `fconnect_cycle` packaged as a uniqueness
statement, and it is how the rings of the construction steps below are
computed. -/

section OrbitCycle

/-- Transferring a cyclic chain along an implied link relation. -/
theorem IsCyclicChain.congr {e e' : D → D → Prop} (h : ∀ ⦃x y : D⦄, e x y → e' x y)
    {p : List D} (hp : IsCyclicChain e p) : IsCyclicChain e' p :=
  ⟨hp.isChain.imp h, fun a ha b hb => h (hp.2 a ha b hb)⟩

/-- Reversing a cyclic chain gives a cyclic chain for the reversed relation. -/
theorem IsCyclicChain.reverse {e : D → D → Prop} {p : List D} (h : IsCyclicChain e p) :
    IsCyclicChain (fun u v => e v u) p.reverse := by
  refine ⟨List.isChain_reverse.mpr h.isChain, fun a ha b hb => ?_⟩
  rw [List.getLast?_reverse] at ha
  rw [List.head?_reverse] at hb
  exact h.2 b hb a ha

variable [Finite D]

omit [Finite D] in
/-- A chain of images of a permutation lists the iterates of its head. -/
theorem eq_map_range_of_isChain {f : Perm D} :
    ∀ (r : List D) (x : D), List.IsChain (fun u v => v = f u) r → r.headD x = x →
      r = (List.range r.length).map fun i => (f ^ i) x := by
  intro r
  induction r with
  | nil => intro x _ _; simp
  | cons a t ih =>
    intro x hchain hhd
    simp only [List.headD_cons] at hhd
    subst hhd
    rw [List.isChain_cons] at hchain
    obtain ⟨h1, h2⟩ := hchain
    match t with
    | [] => simp
    | b :: t' =>
      have hb : b = f a := h1 b rfl
      subst hb
      have ht := ih (f a) h2 (by simp)
      have hfun : ((fun i => (f ^ i) a) ∘ Nat.succ) = fun i => (f ^ i) (f a) := by
        funext i; simp [pow_succ, Perm.mul_apply]
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, hfun]
      exact congrArg₂ List.cons (by simp) ht

/-- The orbit list of `x` is a cyclic chain. -/
theorem isCyclicChain_orbitList (f : Perm D) (x : D) :
    IsCyclicChain (fun u v => v = f u) (orbitList f x) := by
  refine ⟨isChain_orbitList f x, fun a ha b hb => ?_⟩
  have hlast : (orbitList f x).getLastD x = a := by
    rw [List.getLastD_eq_getLast?, Option.mem_def.mp ha]; rfl
  have hhead : b = x := by
    have hx := head_orbitList f x
    rw [List.headD_eq_head?, Option.mem_def.mp hb] at hx
    exact hx
  rw [hhead, ← apply_getLastD_orbitList f x, hlast]

omit [Finite D] in
/-- Reading off an entry of an orbit list. -/
theorem getElem?_orbitList (f : Perm D) (x : D) {i : ℕ}
    (hi : i < Function.minimalPeriod f x) : (orbitList f x)[i]? = some ((f ^ i) x) := by
  rw [orbitList, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- Rotating an orbit list gives the orbit list of the corresponding iterate. -/
theorem rotate_orbitList (f : Perm D) (x : D) (n : ℕ) :
    (orbitList f x).rotate n = orbitList f ((f ^ n) x) := by
  have hmod : ∀ k : ℕ, (f ^ (k % Function.minimalPeriod f x)) x = (f ^ k) x := by
    intro k
    have hk := Function.iterate_mod_minimalPeriod_eq (f := (f : D → D)) (x := x) (n := k)
    rwa [Perm.iterate_eq_pow, Perm.iterate_eq_pow] at hk
  have hget : ∀ (y : D) (j : ℕ) (hj : j < (orbitList f y).length),
      (orbitList f y)[j] = (f ^ j) y := by
    intro y j hj
    have hy := getElem?_orbitList f y (by rwa [← length_orbitList])
    rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hy
    exact hy
  have hm : Function.minimalPeriod f ((f ^ n) x) = Function.minimalPeriod f x := by
    have hi := Function.minimalPeriod_apply_iterate (Hypermap.mem_periodicPts f x) n
    rwa [Perm.iterate_eq_pow] at hi
  have hlen : ((orbitList f x).rotate n).length = (orbitList f ((f ^ n) x)).length := by
    rw [List.length_rotate, length_orbitList, length_orbitList, hm]
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  rw [List.getElem_rotate, hget, hget, length_orbitList, hmod (i + n), pow_add,
    Perm.mul_apply]

/-- **Uniqueness of orbit lists**: a duplicate-free cyclic chain for `f` is the
orbit list of its head. -/
theorem eq_orbitList_of_isCyclicChain {f : Perm D} {r : List D} {x : D}
    (hcyc : IsCyclicChain (fun u v => v = f u) r) (hnd : r.Nodup) (hne : r ≠ [])
    (hhd : r.headD x = x) : r = orbitList f x := by
  have hnpos : 0 < r.length := by
    cases r with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hmap := eq_map_range_of_isChain r x hcyc.isChain hhd
  have hget : ∀ i, i < r.length → r[i]? = some ((f ^ i) x) := by
    intro i hi
    conv_lhs => rw [hmap]
    rw [List.getElem?_map, List.getElem?_range hi]
    rfl
  have hlastq : r.getLast? = some ((f ^ (r.length - 1)) x) := by
    rw [List.getLast?_eq_getElem?]
    exact hget (r.length - 1) (Nat.sub_lt hnpos Nat.one_pos)
  have hheadq : r.head? = some x := by
    rw [List.head?_eq_getElem?]
    simpa using hget 0 hnpos
  have hper : (f ^ r.length) x = x := by
    have hw : x = f ((f ^ (r.length - 1)) x) :=
      hcyc.2 _ (Option.mem_def.mpr hlastq) _ (Option.mem_def.mpr hheadq)
    have hstep : f ((f ^ (r.length - 1)) x) = (f ^ r.length) x := by
      rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hnpos]
    rw [hstep] at hw
    exact hw.symm
  have hdvd : Function.minimalPeriod f x ∣ r.length := by
    rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    change f^[r.length] x = x
    rwa [Perm.iterate_eq_pow]
  have hmpos : 0 < Function.minimalPeriod f x := minimalPeriod_pos f x
  have hle : Function.minimalPeriod f x ≤ r.length := Nat.le_of_dvd hnpos hdvd
  have heq : r.length = Function.minimalPeriod f x := by
    rcases Nat.lt_or_ge (Function.minimalPeriod f x) r.length with hlt | hge
    · exfalso
      have h0 : r[0]'hnpos = x := by
        have := hget 0 hnpos
        rw [List.getElem?_eq_getElem hnpos, Option.some.injEq] at this
        simpa using this
      have hm : r[Function.minimalPeriod f x]'hlt = x := by
        have := hget _ hlt
        rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at this
        rw [this]
        exact pow_minimalPeriod f x
      have h01 := (hnd.getElem_inj_iff (i := 0) (j := Function.minimalPeriod f x)
        (hi := hnpos) (hj := hlt)).mp (by rw [h0, hm])
      omega
    · omega
  rw [hmap, heq, orbitList]

end OrbitCycle

/-! ### Configuration construction programs -/

/-- A basic step of a configuration construction program. -/
inductive CpStep where
  /-- Rotate the start point `n` steps around the outer ring (a no-op on
  overflow). -/
  | R (n : ℕ) : CpStep
  /-- Rotate the start point one step backwards. -/
  | R' : CpStep
  /-- Add a new Y junction and a new face. -/
  | Y : CpStep
  /-- Add a new H junction and a new face, closing an inner face. -/
  | H : CpStep
  /-- Add a new face with no junction (a U-shaped loop). -/
  | U : CpStep
  /-- Add a new K (inverted Y) junction, closing off a face. -/
  | K : CpStep
  /-- Add an inverted-V junction, merging the neighbours of a face. -/
  | A : CpStep
  deriving DecidableEq

/-- A configuration map construction program.  It is interpreted right to left,
starting from a single edge. -/
abbrev CProg := List CpStep

namespace CpStep

/-- The steps that preserve cubic maps: `R`, `U`, `Y` and `H`. -/
def IsCubic : CpStep → Prop
  | .R _ => True
  | .U => True
  | .Y => True
  | .H => True
  | _ => False

/-- The steps allowed in a configuration program: `R`, `Y` and `H`. -/
def IsConfig : CpStep → Prop
  | .R _ => True
  | .Y => True
  | .H => True
  | _ => False

/-- A configuration step is a cubic step. -/
theorem IsConfig.isCubic {s : CpStep} (h : s.IsConfig) : s.IsCubic := by
  cases s <;> simp_all [IsConfig, IsCubic]

end CpStep

/-- `cp` consists only of `R`, `U`, `Y` and `H` steps. -/
def CubicProg (cp : CProg) : Prop := ∀ s ∈ cp, s.IsCubic

/-- `cp` consists only of `R`, `Y` and `H` steps and ends with a `Y` step, so
that the construction starts from a `Y` step. -/
def ConfigProg (cp : CProg) : Prop :=
  (∀ s ∈ cp, s.IsConfig) ∧ cp.getLast? = some .Y

/-- A configuration program is a cubic program. -/
theorem ConfigProg.cubicProg {cp : CProg} (h : ConfigProg cp) : CubicProg cp :=
  fun s hs => (h.1 s hs).isCubic

/-- A configuration program is not empty. -/
theorem ConfigProg.ne_nil {cp : CProg} (h : ConfigProg cp) : cp ≠ [] := by
  rintro rfl
  exact absurd h.2 (by simp)

/-- Peeling a step off a configuration program. -/
theorem ConfigProg.of_cons {s : CpStep} {cp : CProg} (h : ConfigProg (s :: cp))
    (hcp : cp ≠ []) : ConfigProg cp := by
  refine ⟨fun t ht => h.1 t (List.mem_cons_of_mem s ht), ?_⟩
  have h2 := h.2
  match cp, hcp with
  | b :: t, _ => rwa [List.getLast?_cons_cons] at h2

/-- The empty program is cubic. -/
theorem cubicProg_nil : CubicProg [] := by simp [CubicProg]

/-- Peeling a step off a cubic program. -/
theorem CubicProg.of_cons {s : CpStep} {cp : CProg} (h : CubicProg (s :: cp)) :
    CubicProg cp := fun t ht => h t (List.mem_cons_of_mem s ht)

/-- The head step of a cubic program. -/
theorem CubicProg.head {s : CpStep} {cp : CProg} (h : CubicProg (s :: cp)) :
    s.IsCubic := h s List.mem_cons_self

/-- A configuration descriptor: a construction program together with a
reducibility contract and a symmetry flag. -/
structure Config where
  /-- Whether the configuration is symmetric, so that its reflection need not be
  checked when scanning for reducible patterns. -/
  sym : Bool
  /-- The reducibility contract, as indices of contract edges in the
  construction process. -/
  contract : List ℕ
  /-- The construction program of the configuration map. -/
  prog : CProg

/-! ### The ring of a pointed hypermap -/

namespace Hypermap

section CpRing

variable [Finite D] (G : Hypermap D) (x₀ : D)

omit [Finite D] in
/-- Cancelling `node` on the left. -/
theorem inv_node_node (x : D) : G.node⁻¹ (G.node x) = x := G.node.symm_apply_apply x

omit [Finite D] in
/-- Cancelling `node` on the right. -/
theorem node_inv_node (x : D) : G.node (G.node⁻¹ x) = x := G.node.apply_symm_apply x

omit [Finite D] in
/-- `face (edge x)` is the inverse node image of `x`. -/
theorem face_edge (x : D) : G.face (G.edge x) = G.node⁻¹ x := by
  rw [eq_comm, Perm.inv_eq_iff_eq]
  exact (G.edgeK x).symm

/-- The ring of a pointed hypermap: the reverse N-cycle of darts on the node of
`x₀`, starting at `node x₀`.  Unless it is trivial it reads
`node x₀ :: x₀ :: face (edge x₀) :: …`. -/
noncomputable def cpring : List D := orbitList G.node⁻¹ (G.node x₀)

/-- The ring of `x₀` is nontrivial, i.e. has more than one dart. -/
def ProperCpring : Prop := x₀ ≠ G.node x₀

/-- The ring of `x₀` is long, i.e. has more than two darts. -/
def LongCpring : Prop := G.face (G.edge x₀) ≠ G.node x₀

variable {G x₀}

/-- The ring is never empty. -/
theorem cpring_ne_nil : G.cpring x₀ ≠ [] := orbitList_ne_nil _ _

omit [Finite D] in
/-- The ring has no repetitions. -/
theorem nodup_cpring : (G.cpring x₀).Nodup := nodup_orbitList _ _

/-- The ring of `x₀` lists exactly the darts of the node of `x₀`. -/
theorem mem_cpring {x : D} : x ∈ G.cpring x₀ ↔ G.CNode x₀ x := by
  rw [cpring, mem_orbitList, sameCycle_inv, sameCycle_apply_left]

/-- The length of the ring is the size of the node of `x₀`. -/
theorem length_cpring : (G.cpring x₀).length = Function.minimalPeriod G.node x₀ := by
  rw [cpring, length_orbitList, minimalPeriod_inv,
    Function.minimalPeriod_apply (mem_periodicPts G.node x₀)]

omit [Finite D] in
/-- Reading off an entry of the ring. -/
theorem getElem?_cpring {i : ℕ} (hi : i < (G.cpring x₀).length) :
    (G.cpring x₀)[i]? = some (((G.node⁻¹) ^ i) (G.node x₀)) :=
  getElem?_orbitList _ _ (by rw [← length_orbitList]; exact hi)

/-- The ring is a reverse N-cycle. -/
theorem isCyclicChain_cpring : IsCyclicChain (fun u v => u = G.node v) (G.cpring x₀) :=
  (isCyclicChain_orbitList G.node⁻¹ (G.node x₀)).congr (by rintro u v rfl; simp)

/-- The reversed ring is an N-cycle. -/
theorem isCyclicChain_reverse_cpring :
    IsCyclicChain (fun u v => v = G.node u) (G.cpring x₀).reverse :=
  isCyclicChain_cpring.reverse

/-- The ring starts at `node x₀`. -/
theorem headD_cpring : (G.cpring x₀).headD (G.node x₀) = G.node x₀ := head_orbitList _ _

/-- The ring starts at `node x₀`. -/
theorem head_cpring : G.cpring x₀ = G.node x₀ :: (G.cpring x₀).tail := by
  have h := headD_cpring (G := G) (x₀ := x₀)
  match hl : G.cpring x₀ with
  | [] => exact absurd hl cpring_ne_nil
  | a :: t =>
    rw [hl] at h
    simp only [List.headD_cons] at h
    rw [h]
    rfl

/-- **Uniqueness of the ring**: the ring of `x₀` is the only duplicate-free
reverse N-cycle that starts at `node x₀`. -/
theorem cpring_eq {p : List D} (hcyc : IsCyclicChain (fun u v => u = G.node v) p)
    (hnd : p.Nodup) (hne : p ≠ []) (hhd : p.headD (G.node x₀) = G.node x₀) :
    G.cpring x₀ = p :=
  (eq_orbitList_of_isCyclicChain (hcyc.congr (by rintro u v rfl; simp)) hnd hne hhd).symm

/-- A ring is nontrivial exactly when it has more than one dart. -/
theorem proper_cpring_iff : G.ProperCpring x₀ ↔ 1 < (G.cpring x₀).length := by
  rw [length_cpring, ProperCpring]
  have hpos : 0 < Function.minimalPeriod G.node x₀ := minimalPeriod_pos G.node x₀
  constructor
  · intro h
    rcases Nat.lt_or_ge 1 (Function.minimalPeriod G.node x₀) with h1 | h1
    · exact h1
    · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp (by omega)).symm h
  · intro h hfix
    have : Function.minimalPeriod G.node x₀ = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfix.symm
    omega

/-- A ring is long exactly when it has more than two darts. -/
theorem long_cpring_iff : G.LongCpring x₀ ↔ 2 < (G.cpring x₀).length := by
  have hpos : 0 < Function.minimalPeriod G.node x₀ := minimalPeriod_pos G.node x₀
  have hA : G.face (G.edge x₀) = G.node x₀ ↔ G.node (G.node x₀) = x₀ := by
    rw [face_edge, Perm.inv_eq_iff_eq, eq_comm]
  have hB : G.node (G.node x₀) = x₀ ↔ Function.minimalPeriod G.node x₀ ∣ 2 := by
    rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    constructor
    · intro h
      change G.node^[2] x₀ = x₀
      simpa using h
    · intro h
      have h2 : G.node^[2] x₀ = x₀ := h
      simpa using h2
  rw [LongCpring, length_cpring, ne_eq, hA, hB]
  constructor
  · intro h
    by_contra hc
    have hm : Function.minimalPeriod G.node x₀ = 1 ∨ Function.minimalPeriod G.node x₀ = 2 := by
      omega
    refine h ?_
    rcases hm with hm | hm
    · rw [hm]; norm_num
    · rw [hm]
  · intro h hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    omega

omit [Finite D] in
/-- A ring is long exactly when the two ring neighbours of `x₀` differ. -/
theorem longCpring_iff_inv_ne : G.LongCpring x₀ ↔ G.node⁻¹ x₀ ≠ G.node x₀ := by
  unfold LongCpring
  rw [face_edge]

/-- A nontrivial ring starts `node x₀ :: x₀ :: …`. -/
theorem head_proper_cpring (h : G.ProperCpring x₀) :
    G.cpring x₀ = G.node x₀ :: x₀ :: (G.cpring x₀).drop 2 := by
  have hlen : 1 < (G.cpring x₀).length := proper_cpring_iff.mp h
  have h0 := getElem?_cpring (G := G) (x₀ := x₀) (i := 0) (by omega)
  have h1 := getElem?_cpring (G := G) (x₀ := x₀) (i := 1) hlen
  simp only [pow_zero, pow_one, Perm.one_apply, inv_node_node] at h0 h1
  match hl : G.cpring x₀ with
  | [] => rw [hl] at hlen; simp at hlen
  | [a] => rw [hl] at hlen; simp at hlen
  | a :: b :: t =>
    rw [hl] at h0 h1
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    rw [h0, h1]
    rfl

/-- A long ring starts `node x₀ :: x₀ :: face (edge x₀) :: …`. -/
theorem head_long_cpring (h : G.LongCpring x₀) :
    G.cpring x₀ = G.node x₀ :: x₀ :: G.face (G.edge x₀) :: (G.cpring x₀).drop 3 := by
  have hlen : 2 < (G.cpring x₀).length := long_cpring_iff.mp h
  have h0 := getElem?_cpring (G := G) (x₀ := x₀) (i := 0) (by omega)
  have h1 := getElem?_cpring (G := G) (x₀ := x₀) (i := 1) (by omega)
  have h2 := getElem?_cpring (G := G) (x₀ := x₀) (i := 2) hlen
  rw [face_edge]
  simp only [pow_zero, pow_one, Perm.one_apply, pow_two, Perm.mul_apply,
    inv_node_node] at h0 h1 h2
  match hl : G.cpring x₀ with
  | [] => rw [hl] at hlen; simp at hlen
  | [a] => rw [hl] at hlen; simp at hlen
  | [a, b] => rw [hl] at hlen; simp at hlen
  | a :: b :: c :: t =>
    rw [hl] at h0 h1 h2
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2
    rw [h0, h1, h2]
    rfl

/-- A long ring is nontrivial. -/
theorem LongCpring.properCpring (h : G.LongCpring x₀) : G.ProperCpring x₀ :=
  proper_cpring_iff.mpr (by have := long_cpring_iff.mp h; omega)

/-- The ring is nonempty. -/
theorem length_cpring_pos : 0 < (G.cpring x₀).length := by
  rw [length_cpring]; exact minimalPeriod_pos _ _

/-- The ring of `x₀` is closed under `node`. -/
theorem mem_cpring_node_iff {x : D} : G.node x ∈ G.cpring x₀ ↔ x ∈ G.cpring x₀ := by
  rw [mem_cpring, mem_cpring]
  exact ⟨fun hc => hc.trans (G.cnode_node x).symm, fun hc => hc.trans (G.cnode_node x)⟩

/-- A dart whose node image is `x₀` lies on the ring of `x₀`. -/
theorem mem_cpring_of_node {y : D} (hy : G.node y = x₀) : y ∈ G.cpring x₀ := by
  refine mem_cpring.mpr ?_
  have hc : G.CNode y (G.node y) := G.cnode_node y
  rw [hy] at hc
  exact hc.symm

/-- A dart whose second node image is `x₀` lies on the ring of `x₀`. -/
theorem mem_cpring_of_node2 {y : D} (hy : G.node (G.node y) = x₀) : y ∈ G.cpring x₀ := by
  refine mem_cpring.mpr ?_
  have hc : G.CNode y (G.node (G.node y)) := (G.cnode_node y).trans (G.cnode_node (G.node y))
  rw [hy] at hc
  exact hc.symm

/-- The reference dart lies on its own ring. -/
theorem self_mem_cpring : x₀ ∈ G.cpring x₀ := mem_cpring.mpr (SameCycle.refl _ _)

/-- The node image of the reference dart lies on its ring. -/
theorem node_mem_cpring : G.node x₀ ∈ G.cpring x₀ := mem_cpring.mpr (G.cnode_node x₀)

/-- The inverse node image of the reference dart lies on its ring. -/
theorem node_inv_mem_cpring : G.node⁻¹ x₀ ∈ G.cpring x₀ :=
  mem_cpring_of_node (node_inv_node G x₀)

end CpRing

end Hypermap

/-! ### Orbits, iteration and transpositions

The face maps of the extension steps below all have the shape "the face map of
the base map, extended to the new darts, composed with one or two
transpositions".  These two lemmas turn such a description into a description of
the face orbits: one step of a transposition merges two orbits, and merging is
`Setoid.adjoin`. -/

section SameCycleAux

variable [Finite D]

/-- On a finite dart type two darts lie on a common orbit exactly when one is a
nonnegative iterate of the other. -/
theorem sameCycle_iff_exists_pow (f : Perm D) (x y : D) :
    f.SameCycle x y ↔ ∃ n : ℕ, (f ^ n) x = y := by
  refine ⟨fun h => exists_pow_of_reflTransGen ((sameCycle_iff_reflTransGen f x y).mp h), ?_⟩
  rintro ⟨n, rfl⟩
  exact ⟨(n : ℤ), by simp⟩

variable [DecidableEq D]

/-- Multiplying a permutation by a transposition of two darts lying on
*different* orbits merges exactly those two orbits and leaves the others
alone. -/
theorem sameCycle_swap_mul {g : Perm D} {a b : D} (hab : a ≠ b)
    (h : ¬ g.SameCycle a b) (x y : D) :
    (Equiv.swap a b * g).SameCycle x y ↔
      g.SameCycle x y ∨ (g.SameCycle x a ∧ g.SameCycle y b)
        ∨ (g.SameCycle x b ∧ g.SameCycle y a) := by
  classical
  have _ : Fintype D := Fintype.ofFinite D
  have hs : (Equiv.swap a b * g).SameCycle a b := (sameCycle_swap_mul_iff g hab).mpr h
  have hEq : SameCycle.setoid (Equiv.swap a b * g)
      = Setoid.adjoin (SameCycle.setoid g) a b :=
    (Setoid.adjoin_eq_self_of hs).symm.trans (adjoin_sameCycle_swap_mul g a b)
  have hrel : (Equiv.swap a b * g).SameCycle x y
      ↔ (Setoid.adjoin (SameCycle.setoid g) a b) x y := by rw [← hEq]; exact Iff.rfl
  rw [hrel, Setoid.adjoin_iff]
  exact Iff.rfl

/-- The identity permutation has one orbit per dart. -/
private theorem cycleCount_one {α : Type*} [Finite α] :
    cycleCount (1 : Perm α) = Nat.card α := by
  refine (Nat.card_eq_of_bijective (Quotient.mk (SameCycle.setoid (1 : Perm α))) ⟨?_, ?_⟩).symm
  · intro x y h
    obtain ⟨i, hi⟩ := Quotient.exact h
    rwa [one_zpow, Equiv.Perm.one_apply] at hi
  · exact Quotient.ind fun x => ⟨x, rfl⟩

end SameCycleAux

/-! ### Connectivity criteria

A hypermap is connected exactly when all its darts are joined by chains of
`GLink` steps; the extension steps below are shown connected by exhibiting such
a chain from every dart to the new dart `X`. -/

section ConnectedAux

/-- Transporting component links along a map of dart types. -/
private theorem eqvGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (hf : ∀ x y, r x y → Relation.EqvGen s (f x) (f y)) {x y : α}
    (h : Relation.EqvGen r x y) : Relation.EqvGen s (f x) (f y) := by
  induction h with
  | rel a b hab => exact hf a b hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A hypermap all of whose darts are linked to one fixed dart is connected. -/
private theorem Hypermap.connected_of_forall_eqvGen (H : Hypermap D) (z : D)
    (h : ∀ u : D, Relation.EqvGen H.GLink u z) : H.Connected := by
  have hcard : Nat.card (Quotient H.gcompSetoid) = 1 := by
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨?_⟩, ⟨Quotient.mk H.gcompSetoid z⟩⟩
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound (Relation.EqvGen.trans _ _ _ (h a)
      (Relation.EqvGen.symm _ _ (h b)))
  exact hcard

/-- In a connected hypermap any two darts are linked. -/
private theorem Hypermap.eqvGen_glink_of_connected {H : Hypermap D} (h : H.Connected)
    (x y : D) : Relation.EqvGen H.GLink x y := by
  have hsub : Subsingleton (Quotient H.gcompSetoid) := (Nat.card_eq_one_iff_unique.mp h).1
  exact Quotient.exact (Subsingleton.elim (Quotient.mk H.gcompSetoid x)
    (Quotient.mk H.gcompSetoid y))

end ConnectedAux

/-! ### Reversing the perimeter -/

section QuasicubicAux

/-- Cubicity away from a list only depends on the darts it contains. -/
private theorem Hypermap.quasicubic_reverse {H : Hypermap D} {r : List D}
    (h : H.Quasicubic r) : H.Quasicubic r.reverse :=
  ⟨fun x hx => h.node_node_node (by simpa using hx),
    fun x hx => h.node_ne (by simpa using hx)⟩

end QuasicubicAux


/-! ### Extended dart types

Both basic extension steps add a single edge, i.e. two darts, to the dart type.
They share this concrete two-point extension, which behaves better under case
analysis than a general sum type. -/

/-- The darts of `A` extended with the two darts `X` and `Xe` of a new edge. -/
inductive EcpDart (A : Type*) where
  /-- The first new dart. -/
  | X : EcpDart A
  /-- The second new dart, the edge image of `X`. -/
  | Xe : EcpDart A
  /-- The image of an old dart. -/
  | icp (x : A) : EcpDart A
  deriving DecidableEq

namespace EcpDart

variable {A : Type*}

/-- Extending a dart type by two darts is adding two elements. -/
def equivOption (A : Type*) : EcpDart A ≃ Option (Option A) where
  toFun u := match u with
    | .X => none
    | .Xe => some none
    | .icp x => some (some x)
  invFun o := match o with
    | none => .X
    | some none => .Xe
    | some (some x) => .icp x
  left_inv u := by cases u <;> rfl
  right_inv o := by rcases o with _ | (_ | x) <;> rfl

instance [Finite A] : Finite (EcpDart A) := Finite.of_equiv _ (equivOption A).symm

/-- The injection of old darts is injective. -/
theorem icp_injective : Function.Injective (icp : A → EcpDart A) := by
  intro x y h; cases h; rfl

@[simp] theorem icp_inj {x y : A} : (icp x : EcpDart A) = icp y ↔ x = y :=
  icp_injective.eq_iff

/-- Extending a dart type adds two darts. -/
theorem card_eq [Finite A] : Nat.card (EcpDart A) = Nat.card A + 2 := by
  rw [Nat.card_congr (equivOption A), Finite.card_option, Finite.card_option]

/-! #### Extending a permutation to the new darts -/

/-- The underlying map of `EcpDart.extend`. -/
def extendFun (f : A → A) : EcpDart A → EcpDart A
  | .X => .X
  | .Xe => .Xe
  | .icp x => .icp (f x)

/-- A permutation of `A`, extended to `EcpDart A` by fixing the two new darts.
The face map of each extension step is this extension of the face map of the
base map, composed with one or two transpositions. -/
def extend (f : Equiv.Perm A) : Equiv.Perm (EcpDart A) where
  toFun := extendFun f
  invFun := extendFun f.symm
  left_inv u := by cases u <;> simp [extendFun]
  right_inv u := by cases u <;> simp [extendFun]

@[simp] theorem extend_X (f : Equiv.Perm A) : extend f .X = .X := rfl

@[simp] theorem extend_Xe (f : Equiv.Perm A) : extend f .Xe = .Xe := rfl

@[simp] theorem extend_icp (f : Equiv.Perm A) (x : A) :
    extend f (.icp x) = .icp (f x) := rfl

/-- An extended permutation fixes the first new dart. -/
theorem extend_pow_X (f : Equiv.Perm A) (n : ℕ) : ((extend f) ^ n) .X = .X := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, ih, extend_X]

/-- An extended permutation fixes the second new dart. -/
theorem extend_pow_Xe (f : Equiv.Perm A) (n : ℕ) : ((extend f) ^ n) .Xe = .Xe := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, ih, extend_Xe]

/-- An extended permutation acts on old darts as the original one. -/
theorem extend_pow_icp (f : Equiv.Perm A) (n : ℕ) (x : A) :
    ((extend f) ^ n) (.icp x) = .icp ((f ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih, extend_icp]

variable [Finite A]

/-- The first new dart is its own orbit of an extended permutation. -/
theorem sameCycle_extend_X_left (f : Equiv.Perm A) (u : EcpDart A) :
    (extend f).SameCycle .X u ↔ u = .X := by
  rw [sameCycle_iff_exists_pow]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, rfl⟩; rw [extend_pow_X]
  · rintro rfl; exact ⟨0, by simp⟩

/-- The first new dart is its own orbit of an extended permutation. -/
theorem sameCycle_extend_X_right (f : Equiv.Perm A) (u : EcpDart A) :
    (extend f).SameCycle u .X ↔ u = .X := by
  refine ⟨fun h => (sameCycle_extend_X_left f u).mp h.symm, ?_⟩
  rintro rfl
  exact Equiv.Perm.SameCycle.refl _ _

/-- The second new dart is its own orbit of an extended permutation. -/
theorem sameCycle_extend_Xe_left (f : Equiv.Perm A) (u : EcpDart A) :
    (extend f).SameCycle .Xe u ↔ u = .Xe := by
  rw [sameCycle_iff_exists_pow]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, rfl⟩; rw [extend_pow_Xe]
  · rintro rfl; exact ⟨0, by simp⟩

/-- The second new dart is its own orbit of an extended permutation. -/
theorem sameCycle_extend_Xe_right (f : Equiv.Perm A) (u : EcpDart A) :
    (extend f).SameCycle u .Xe ↔ u = .Xe := by
  refine ⟨fun h => (sameCycle_extend_Xe_left f u).mp h.symm, ?_⟩
  rintro rfl
  exact Equiv.Perm.SameCycle.refl _ _

/-- Extending a permutation does not change the orbits of the old darts. -/
theorem sameCycle_extend_icp (f : Equiv.Perm A) (x y : A) :
    (extend f).SameCycle (.icp x) (.icp y) ↔ f.SameCycle x y := by
  rw [sameCycle_iff_exists_pow, sameCycle_iff_exists_pow]
  constructor
  · rintro ⟨n, hn⟩
    rw [extend_pow_icp] at hn
    exact ⟨n, icp_injective hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [extend_pow_icp]⟩

/-- Extending a permutation adds two orbits. -/
theorem cycleCount_extend (f : Equiv.Perm A) :
    cycleCount (extend f) = cycleCount f + 2 := by
  classical
  have hwd : ∀ x y : A, (SameCycle.setoid f).r x y →
      Quotient.mk (SameCycle.setoid (extend f)) (EcpDart.icp x)
        = Quotient.mk (SameCycle.setoid (extend f)) (EcpDart.icp y) :=
    fun _ _ h => Quotient.sound ((sameCycle_extend_icp f _ _).mpr h)
  set φ : Quotient (SameCycle.setoid f) → Quotient (SameCycle.setoid (extend f)) :=
    Quotient.lift (fun x => Quotient.mk (SameCycle.setoid (extend f)) (EcpDart.icp x)) hwd
    with hφ
  set ψ : Option (Option (Quotient (SameCycle.setoid f))) →
      Quotient (SameCycle.setoid (extend f)) :=
    fun o => o.elim (Quotient.mk (SameCycle.setoid (extend f)) .X)
      (fun o' => o'.elim (Quotient.mk (SameCycle.setoid (extend f)) .Xe) φ) with hψ
  have hXe : ∀ x : A, Quotient.mk (SameCycle.setoid (extend f)) (EcpDart.Xe)
      ≠ Quotient.mk (SameCycle.setoid (extend f)) (EcpDart.icp x) := by
    intro x hx
    exact absurd ((sameCycle_extend_Xe_left f _).mp (Quotient.exact hx)) (by simp)
  have hX : ∀ u : EcpDart A, u ≠ .X →
      Quotient.mk (SameCycle.setoid (extend f)) (EcpDart.X)
        ≠ Quotient.mk (SameCycle.setoid (extend f)) u := by
    intro u hu h
    exact hu ((sameCycle_extend_X_left f _).mp (Quotient.exact h))
  have hbij : Function.Bijective ψ := by
    constructor
    · rintro (_ | (_ | a)) (_ | (_ | b)) hab
      · rfl
      · exact absurd hab (hX _ (by simp))
      · revert hab
        refine Quotient.inductionOn b fun v hab => ?_
        exact absurd hab (hX _ (by simp))
      · exact absurd hab.symm (hX _ (by simp))
      · rfl
      · revert hab
        refine Quotient.inductionOn b fun v hab => ?_
        exact absurd hab (hXe v)
      · revert hab
        refine Quotient.inductionOn a fun u hab => ?_
        exact absurd hab.symm (hX _ (by simp))
      · revert hab
        refine Quotient.inductionOn a fun u hab => ?_
        exact absurd hab.symm (hXe u)
      · revert hab
        refine Quotient.inductionOn₂ a b fun u v hab => ?_
        exact congrArg (fun q => some (some q))
          (Quotient.sound ((sameCycle_extend_icp f u v).mp (Quotient.exact hab)))
    · refine Quotient.ind fun u => ?_
      cases u with
      | X => exact ⟨none, rfl⟩
      | Xe => exact ⟨some none, rfl⟩
      | icp x => exact ⟨some (some (Quotient.mk (SameCycle.setoid f) x)), rfl⟩
  have hcard := Nat.card_eq_of_bijective ψ hbij
  rw [Finite.card_option, Finite.card_option] at hcard
  simp only [cycleCount]
  omega

end EcpDart

/-! ### Building hypermaps from three maps -/

namespace Hypermap

/-- On a finite dart type, three maps with `node ∘ face ∘ edge = id` are
automatically bijective. -/
theorem bijective_of_cancel3 [Finite D] {e n f : D → D} (h : ∀ x, n (f (e x)) = x) :
    Function.Bijective e ∧ Function.Bijective n ∧ Function.Bijective f := by
  have he : Function.Injective e := fun x y hxy => by rw [← h x, ← h y, hxy]
  have hnb : Function.Bijective n :=
    Finite.surjective_iff_bijective.mp fun x => ⟨f (e x), h x⟩
  refine ⟨Finite.injective_iff_bijective.mp he, hnb, ?_⟩
  refine Finite.surjective_iff_bijective.mp fun z => ⟨e (n z), hnb.1 ?_⟩
  rw [h (n z)]

end Hypermap

/-! ### Pointed maps -/

/-- A finite hypermap bundled with a reference dart on its ring.  This is the
reference's `pointed_map`; the dart type has to be part of the bundle because
the construction steps below change it. -/
structure PointedMap where
  /-- The dart type. -/
  Dart : Type
  /-- The dart type is finite. -/
  finite : Finite Dart
  /-- Equality of darts is decidable. -/
  decEq : DecidableEq Dart
  /-- The hypermap. -/
  map : Hypermap Dart
  /-- The reference dart. -/
  point : Dart

attribute [instance] PointedMap.finite PointedMap.decEq

namespace PointedMap

/-- The ring of a pointed map. -/
noncomputable def cpring (M : PointedMap) : List M.Dart := M.map.cpring M.point

/-- The ring of a pointed map is nontrivial. -/
def Proper (M : PointedMap) : Prop := M.map.ProperCpring M.point

/-- The ring of a pointed map is long. -/
def Long (M : PointedMap) : Prop := M.map.LongCpring M.point

end PointedMap

/-! ### The rotation step -/

namespace Hypermap

section EcpR

variable [Finite D] (G : Hypermap D) (x₀ : D)

/-- The reference dart after an `R n` step: `n` reverse node steps from `x₀`.

Unlike the reference, where an `R n` step with `n` at least the ring size is the
identity, here the rotation is taken modulo the ring size; the two agree for all
`n` below the ring size. -/
def ecpRPoint (n : ℕ) : D := ((G.node⁻¹) ^ n) x₀

variable {G x₀}

/-- An `R n` step rotates the ring by `n`. -/
theorem cpring_ecpR (n : ℕ) : G.cpring (G.ecpRPoint x₀ n) = (G.cpring x₀).rotate n := by
  rw [cpring, cpring, ecpRPoint, rotate_orbitList]
  congr 1
  have hc : G.node * (G.node⁻¹) ^ n = (G.node⁻¹) ^ n * G.node :=
    ((Commute.refl G.node).inv_right.pow_right n).eq
  exact congrArg (fun p : Perm D => p x₀) hc

/-- An `R n` step does not change the size of the ring. -/
theorem length_cpring_ecpR (n : ℕ) :
    (G.cpring (G.ecpRPoint x₀ n)).length = (G.cpring x₀).length := by
  rw [cpring_ecpR, List.length_rotate]

/-- An `R n` step does not change the darts of the ring. -/
theorem mem_cpring_ecpR {n : ℕ} {x : D} :
    x ∈ G.cpring (G.ecpRPoint x₀ n) ↔ x ∈ G.cpring x₀ := by
  rw [cpring_ecpR, List.mem_rotate]

/-- An `R n` step preserves quasicubicity. -/
theorem quasicubic_ecpR {n : ℕ} (h : G.Quasicubic (G.cpring x₀)) :
    G.Quasicubic (G.cpring (G.ecpRPoint x₀ n)) := by
  refine ⟨fun x hx => h.node_node_node ?_, fun x hx => h.node_ne ?_⟩ <;>
    exact fun hmem => hx (mem_cpring_ecpR.mpr hmem)

/-- An `R n` step preserves nontriviality of the ring. -/
theorem properCpring_ecpR {n : ℕ} (h : G.ProperCpring x₀) :
    G.ProperCpring (G.ecpRPoint x₀ n) :=
  proper_cpring_iff.mpr (by rw [length_cpring_ecpR]; exact proper_cpring_iff.mp h)

/-- An `R n` step preserves longness of the ring. -/
theorem longCpring_ecpR {n : ℕ} (h : G.LongCpring x₀) :
    G.LongCpring (G.ecpRPoint x₀ n) :=
  long_cpring_iff.mpr (by rw [length_cpring_ecpR]; exact long_cpring_iff.mp h)

/-- An `R (order - 1)` step moves the reference dart to `node x₀`. -/
theorem ecpRPoint_minimalPeriod_sub_one :
    G.ecpRPoint x₀ (Function.minimalPeriod G.node x₀ - 1) = G.node x₀ := by
  have hm : 0 < Function.minimalPeriod G.node x₀ := minimalPeriod_pos _ _
  have hfix : (G.node ^ Function.minimalPeriod G.node x₀) x₀ = x₀ := by
    have h := Function.isPeriodicPt_minimalPeriod G.node x₀
    have h' : G.node^[Function.minimalPeriod G.node x₀] x₀ = x₀ := h
    rwa [Perm.iterate_eq_pow] at h'
  rw [ecpRPoint, inv_pow, Equiv.Perm.inv_eq_iff_eq, ← Perm.mul_apply, ← pow_succ,
    Nat.sub_add_cancel hm]
  exact hfix.symm

end EcpR

end Hypermap

/-! ### List helpers -/

section ListAux

variable {α β : Type*}

/-- The last entry of a mapped list. -/
theorem getLast?_map (f : α → β) (l : List α) : (l.map f).getLast? = l.getLast?.map f := by
  induction l with
  | nil => simp
  | cons a t ih =>
    match t with
    | [] => simp
    | b :: t' =>
      rw [List.map_cons, List.map_cons, List.getLast?_cons_cons, List.getLast?_cons_cons,
        ← List.map_cons, ih]

/-- Dropping the head of a list with at least two entries does not change its
last entry. -/
theorem getLast?_cons_ne_nil {a : α} {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  match l with
  | [] => exact absurd rfl h
  | b :: t => rw [List.getLast?_cons_cons]

end ListAux

/-! ### The U step: a new disconnected face -/

namespace Hypermap

section EcpU

variable [Finite D] [DecidableEq D] (G : Hypermap D) (x₀ : D)

/-- The edge map of the two basic extension steps: it swaps the two new darts
and acts as `edge` on the old ones. -/
def ecpEdge : EcpDart D → EcpDart D
  | .X => .Xe
  | .Xe => .X
  | .icp x => .icp (G.edge x)

/-- The node map of a `U` step. -/
def ecpUNode : EcpDart D → EcpDart D
  | .X => .Xe
  | .Xe => .icp (G.node (G.node x₀))
  | .icp y => if y = G.node x₀ then .X else .icp (G.node y)

/-- The face map of a `U` step. -/
def ecpUFace : EcpDart D → EcpDart D
  | .X => .X
  | .Xe => .icp (G.node x₀)
  | .icp y => if G.face y = G.node x₀ then .Xe else .icp (G.face y)

omit [Finite D] in
/-- The three maps of a `U` step satisfy the hypermap identity. -/
theorem ecpU_cancel3 (u : EcpDart D) : ecpUNode G x₀ (ecpUFace G x₀ (ecpEdge G u)) = u := by
  cases u with
  | X => simp [ecpEdge, ecpUFace, ecpUNode]
  | Xe => simp [ecpEdge, ecpUFace, ecpUNode]
  | icp x =>
    change ecpUNode G x₀ (ecpUFace G x₀ (.icp (G.edge x))) = _
    by_cases h : G.face (G.edge x) = G.node x₀
    · change ecpUNode G x₀ (if G.face (G.edge x) = G.node x₀ then .Xe else _) = _
      rw [ite_eq_left h]
      change (EcpDart.icp (G.node (G.node x₀)) : EcpDart D) = _
      rw [← h, G.edgeK]
    · change ecpUNode G x₀ (if G.face (G.edge x) = G.node x₀ then .Xe else
        .icp (G.face (G.edge x))) = _
      rw [ite_eq_right h]
      change (if G.face (G.edge x) = G.node x₀ then (.X : EcpDart D) else
        .icp (G.node (G.face (G.edge x)))) = _
      rw [ite_eq_right h, G.edgeK]

/-- The hypermap obtained by a `U` step at `x₀`: a new face disjoint from the
rest of the map. -/
noncomputable def ecpUMap : Hypermap (EcpDart D) :=
  ofCancel3 (ecpEdge G) (ecpUNode G x₀) (ecpUFace G x₀) (ecpU_cancel3 G x₀)

@[simp] theorem ecpUMap_edge (u : EcpDart D) : (ecpUMap G x₀).edge u = ecpEdge G u := rfl
@[simp] theorem ecpUMap_node (u : EcpDart D) : (ecpUMap G x₀).node u = ecpUNode G x₀ u := rfl
@[simp] theorem ecpUMap_face (u : EcpDart D) : (ecpUMap G x₀).face u = ecpUFace G x₀ u := rfl

/-- A `U` step preserves plainness. -/
theorem plain_ecpU (h : G.Plain) : (ecpUMap G x₀).Plain := by
  constructor
  · intro u
    cases u with
    | X => rfl
    | Xe => rfl
    | icp x => change (EcpDart.icp (G.edge (G.edge x)) : EcpDart D) = _; rw [h.edge_edge]
  · intro u
    cases u with
    | X => exact fun hu => by cases hu
    | Xe => exact fun hu => by cases hu
    | icp x =>
      intro hu
      exact h.edge_ne x (EcpDart.icp_injective hu)

/-- The ring after a `U` step. -/
theorem cpring_ecpU :
    (ecpUMap G x₀).cpring .X = .Xe :: .X :: (G.cpring x₀).map EcpDart.icp := by
  obtain ⟨t, ht⟩ : ∃ t, G.cpring x₀ = G.node x₀ :: t := ⟨_, head_cpring⟩
  have hhead : (G.cpring x₀).head? = some (G.node x₀) := by rw [ht]; rfl
  have hnd0 : (G.cpring x₀).Nodup := nodup_cpring
  have htail : ∀ b ∈ t, b ≠ G.node x₀ := by
    intro b hb hbe
    rw [ht, List.nodup_cons] at hnd0
    exact hnd0.1 (hbe ▸ hb)
  have hlast : ∀ a ∈ (G.cpring x₀).getLast?, a = G.node (G.node x₀) := fun a ha =>
    isCyclicChain_cpring.2 a ha (G.node x₀) hhead
  refine cpring_eq ?_ ?_ (by simp) rfl
  · constructor
    · rw [List.isChain_cons_cons]
      refine ⟨rfl, ?_⟩
      rw [List.isChain_cons]
      constructor
      · intro y hy
        rw [List.head?_map, hhead, Option.map_some] at hy
        obtain rfl : y = EcpDart.icp (G.node x₀) := (Option.some.injEq _ _).mp hy.symm
        change (EcpDart.X : EcpDart D) = if G.node x₀ = G.node x₀ then .X else _
        rw [ite_eq_left rfl]
      · rw [List.isChain_map]
        refine isCyclicChain_cpring.isChain.imp_of_mem_tail_imp ?_
        intro a b _ hb hab
        rw [ht] at hb
        have hbne : b ≠ G.node x₀ := htail b hb
        change (EcpDart.icp a : EcpDart D) = if b = G.node x₀ then .X else .icp (G.node b)
        rw [ite_eq_right hbne, hab]
    · intro a ha b hb
      obtain rfl : b = EcpDart.Xe := (Option.some.injEq _ _).mp hb.symm
      rw [getLast?_cons_ne_nil (by simp), getLast?_cons_ne_nil (by simp [ht]),
        getLast?_map] at ha
      obtain ⟨c, hc, rfl⟩ := Option.mem_map.mp ha
      change (EcpDart.icp c : EcpDart D) = .icp (G.node (G.node x₀))
      rw [hlast c hc]
  · refine List.nodup_cons.mpr ⟨by simp, List.nodup_cons.mpr ⟨by simp, ?_⟩⟩
    exact hnd0.map EcpDart.icp_injective

/-- A `U` step adds two darts to the ring. -/
theorem length_cpring_ecpU :
    ((ecpUMap G x₀).cpring .X).length = (G.cpring x₀).length + 2 := by
  rw [cpring_ecpU]
  simp

omit [Finite D] in
/-- The node map of a `U` step away from the head of the ring. -/
theorem ecpUNode_icp_of_ne {y : D} (hy : y ≠ G.node x₀) :
    ecpUNode G x₀ (.icp y) = .icp (G.node y) := ite_eq_right hy

/-- The ring after a `U` step is long. -/
theorem longCpring_ecpU : (ecpUMap G x₀).LongCpring .X := by
  refine long_cpring_iff.mpr ?_
  rw [length_cpring_ecpU]
  have := length_cpring_pos (G := G) (x₀ := x₀)
  omega

/-- The ring after a `U` step is nontrivial. -/
theorem properCpring_ecpU : (ecpUMap G x₀).ProperCpring .X :=
  (longCpring_ecpU G x₀).properCpring

/-- A `U` step preserves quasicubicity. -/
theorem quasicubic_ecpU (h : G.Quasicubic (G.cpring x₀)) :
    (ecpUMap G x₀).Quasicubic ((ecpUMap G x₀).cpring .X) := by
  have key : ∀ u : EcpDart D, u ∉ (ecpUMap G x₀).cpring EcpDart.X →
      ∃ x : D, u = .icp x ∧ x ∉ G.cpring x₀ := by
    intro u hu
    rw [cpring_ecpU] at hu
    cases u with
    | X => exact absurd (by simp) hu
    | Xe => exact absurd (by simp) hu
    | icp x =>
      refine ⟨x, rfl, fun hx => hu ?_⟩
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_map.mpr ⟨x, hx, rfl⟩))))
  have hstep : ∀ x : D, x ∉ G.cpring x₀ →
      ecpUNode G x₀ (.icp x) = .icp (G.node x) := by
    intro x hx
    refine ecpUNode_icp_of_ne G x₀ (fun hc => hx ?_)
    rw [hc]
    exact node_mem_cpring
  have hclosed : ∀ x : D, x ∉ G.cpring x₀ → G.node x ∉ G.cpring x₀ :=
    fun x hx hc => hx (mem_cpring_node_iff.mp hc)
  constructor
  · intro u hu
    obtain ⟨x, rfl, hx⟩ := key u hu
    change ecpUNode G x₀ (ecpUNode G x₀ (ecpUNode G x₀ (.icp x))) = .icp x
    rw [hstep x hx, hstep _ (hclosed x hx), hstep _ (hclosed _ (hclosed x hx)),
      h.node_node_node hx]
  · intro u hu
    obtain ⟨x, rfl, hx⟩ := key u hu
    change ecpUNode G x₀ (.icp x) ≠ .icp x
    rw [hstep x hx]
    exact fun hc => h.node_ne hx (EcpDart.icp_injective hc)

/-! #### Face orbits of a `U` step -/

/-- The face map of a `U` step is the extended face map of `G` composed with the
transposition that splices the new dart `Xe` into the face of `node x₀`. -/
theorem ecpUMap_face_eq :
    (ecpUMap G x₀).face
      = Equiv.swap .Xe (.icp (G.node x₀)) * EcpDart.extend G.face := by
  ext u
  rw [Perm.mul_apply]
  cases u with
  | X =>
    rw [EcpDart.extend_X, Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]
    rfl
  | Xe =>
    rw [EcpDart.extend_Xe, Equiv.swap_apply_left]
    rfl
  | icp y =>
    have hlhs : (ecpUMap G x₀).face (.icp y)
        = if G.face y = G.node x₀ then .Xe else .icp (G.face y) := rfl
    rw [hlhs, EcpDart.extend_icp]
    by_cases hy : G.face y = G.node x₀
    · rw [ite_eq_left hy, hy, Equiv.swap_apply_right]
    · rw [ite_eq_right hy,
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hy)]

omit [DecidableEq D] in
/-- The two darts spliced together by a `U` step lie on different orbits of the
extended face map. -/
private theorem not_sameCycle_extend_ecpU :
    ¬ (EcpDart.extend G.face).SameCycle (.Xe : EcpDart D) (.icp (G.node x₀)) := by
  rw [EcpDart.sameCycle_extend_Xe_left]
  simp

/-- The face orbits of a `U` step are the face orbits of `G` with the orbit of
the new dart `Xe` merged into the face of `node x₀`. -/
theorem sameCycle_face_ecpU (u v : EcpDart D) :
    (ecpUMap G x₀).face.SameCycle u v ↔
      (EcpDart.extend G.face).SameCycle u v
        ∨ ((EcpDart.extend G.face).SameCycle u .Xe
            ∧ (EcpDart.extend G.face).SameCycle v (.icp (G.node x₀)))
        ∨ ((EcpDart.extend G.face).SameCycle u (.icp (G.node x₀))
            ∧ (EcpDart.extend G.face).SameCycle v .Xe) := by
  rw [ecpUMap_face_eq]
  exact sameCycle_swap_mul (by simp) (not_sameCycle_extend_ecpU G x₀) u v

/-- A `U` step adds a face with a single dart: the new dart `X` is alone on its
face orbit. -/
theorem cface_ecpU (u : EcpDart D) : (ecpUMap G x₀).CFace .X u ↔ u = .X := by
  rw [show (ecpUMap G x₀).CFace .X u ↔ _ from sameCycle_face_ecpU G x₀ .X u]
  simp [EcpDart.sameCycle_extend_X_left]

/-- A `U` step does not change the face orbits of the old darts. -/
theorem cface_icpU (x y : D) :
    (ecpUMap G x₀).CFace (.icp x) (.icp y) ↔ G.CFace x y := by
  rw [show (ecpUMap G x₀).CFace (.icp x) (.icp y) ↔ _ from
    sameCycle_face_ecpU G x₀ (.icp x) (.icp y)]
  simp [EcpDart.sameCycle_extend_icp, EcpDart.sameCycle_extend_Xe_right]

/-- The second new dart of a `U` step joins the face of `node x₀`. -/
theorem cface_Xe_icpU (z : D) :
    (ecpUMap G x₀).CFace .Xe (.icp z) ↔ G.CFace z (G.node x₀) := by
  rw [show (ecpUMap G x₀).CFace .Xe (.icp z) ↔ _ from
    sameCycle_face_ecpU G x₀ .Xe (.icp z)]
  simp [EcpDart.sameCycle_extend_icp, EcpDart.sameCycle_extend_Xe_left,
    EcpDart.sameCycle_extend_Xe_right]

/-- Every dart of a `U` step map is on the face of an old dart, or on the new
face. -/
theorem fband_icpU (u : EcpDart D) :
    (∃ x : D, (ecpUMap G x₀).CFace u (.icp x)) ∨ (ecpUMap G x₀).CFace .X u := by
  cases u with
  | X => exact Or.inr (SameCycle.refl _ _)
  | Xe =>
    exact Or.inl ⟨G.node x₀, (cface_Xe_icpU G x₀ (G.node x₀)).mpr (SameCycle.refl _ _)⟩
  | icp x => exact Or.inl ⟨x, SameCycle.refl _ _⟩

/-- A `U` step does not change the adjacency of old darts. -/
theorem adj_icpU (x y : D) :
    (ecpUMap G x₀).Adj (.icp x) (.icp y) ↔ G.Adj x y := by
  constructor
  · rintro ⟨u, hu, hru⟩
    cases u with
    | X => exact absurd ((cface_ecpU G x₀ _).mp hu.symm) (by simp)
    | Xe =>
      have hedge : (ecpUMap G x₀).edge .Xe = .X := rfl
      rw [Rlink, hedge] at hru
      exact absurd ((cface_ecpU G x₀ _).mp hru) (by simp)
    | icp z =>
      have hedge : (ecpUMap G x₀).edge (.icp z) = .icp (G.edge z) := rfl
      rw [Rlink, hedge] at hru
      exact ⟨z, (cface_icpU G x₀ x z).mp hu, (cface_icpU G x₀ _ y).mp hru⟩
  · rintro ⟨z, hz, hrz⟩
    refine ⟨.icp z, (cface_icpU G x₀ x z).mpr hz, ?_⟩
    have hedge : (ecpUMap G x₀).edge (.icp z) = .icp (G.edge z) := rfl
    rw [Rlink, hedge]
    exact (cface_icpU G x₀ _ y).mpr hrz

/-- The new face of a `U` step is adjacent exactly to the face of `node x₀`. -/
theorem adj_ecpU (u : EcpDart D) :
    (ecpUMap G x₀).Adj .X u ↔ (ecpUMap G x₀).Fband [.icp (G.node x₀)] u := by
  have hXe : (ecpUMap G x₀).CFace .Xe (.icp (G.node x₀)) :=
    (cface_Xe_icpU G x₀ (G.node x₀)).mpr (SameCycle.refl _ _)
  constructor
  · rintro ⟨z, hz, hrz⟩
    obtain rfl : z = EcpDart.X := (cface_ecpU G x₀ z).mp hz
    have hedge : (ecpUMap G x₀).edge .X = .Xe := rfl
    rw [Rlink, hedge] at hrz
    exact ⟨.icp (G.node x₀), List.mem_cons_self .., (hXe.symm.trans hrz).symm⟩
  · rintro ⟨v, hv, huv⟩
    obtain rfl : v = EcpDart.icp (G.node x₀) := by simpa using hv
    refine ⟨.X, SameCycle.refl _ _, ?_⟩
    have hedge : (ecpUMap G x₀).edge .X = .Xe := rfl
    rw [Rlink, hedge]
    exact hXe.trans huv.symm

/-- A `U` step preserves bridgelessness. -/
theorem bridgeless_ecpU (h : G.Bridgeless) : (ecpUMap G x₀).Bridgeless := by
  intro u hu
  cases u with
  | X =>
    have hedge : (ecpUMap G x₀).edge .X = .Xe := rfl
    rw [hedge] at hu
    exact absurd ((cface_ecpU G x₀ _).mp hu) (by simp)
  | Xe =>
    have hedge : (ecpUMap G x₀).edge .Xe = .X := rfl
    rw [hedge] at hu
    exact absurd ((cface_ecpU G x₀ _).mp hu.symm) (by simp)
  | icp x =>
    have hedge : (ecpUMap G x₀).edge (.icp x) = .icp (G.edge x) := rfl
    rw [hedge] at hu
    exact h x ((cface_icpU G x₀ x (G.edge x)).mp hu)

/-! #### Connectivity of a `U` step -/

/-- A `U` step preserves connectedness: the new face is attached to the rest of
the map through the new edge. -/
theorem connected_ecpU (h : G.Connected) : (ecpUMap G x₀).Connected := by
  have hXXe : (ecpUMap G x₀).GLink .X .Xe := Or.inl rfl
  have hXeN : (ecpUMap G x₀).GLink .Xe (.icp (G.node (G.node x₀))) := Or.inr (Or.inl rfl)
  have hXeF : (ecpUMap G x₀).GLink .Xe (.icp (G.node x₀)) := Or.inr (Or.inr rfl)
  have hnodeX : (ecpUMap G x₀).node (.icp (G.node x₀)) = .X := ite_eq_left rfl
  have hXn : Relation.EqvGen (ecpUMap G x₀).GLink (.X : EcpDart D) (.icp (G.node x₀)) :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hXXe)
      (Relation.EqvGen.rel _ _ hXeF)
  have key : ∀ x y : D, G.GLink x y →
      Relation.EqvGen (ecpUMap G x₀).GLink (.icp x) (.icp y) := by
    intro x y hxy
    rcases hxy with rfl | rfl | rfl
    · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
    · by_cases hx : x = G.node x₀
      · subst hx
        refine Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ (Or.inr (Or.inl hnodeX.symm))) ?_
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hXXe)
          (Relation.EqvGen.rel _ _ hXeN)
      · exact Relation.EqvGen.rel _ _
          (Or.inr (Or.inl (ecpUNode_icp_of_ne G x₀ hx).symm))
    · by_cases hx : G.face x = G.node x₀
      · have hfx : (ecpUMap G x₀).face (.icp x) = .Xe := ite_eq_left hx
        rw [hx]
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ (Or.inr (Or.inr hfx.symm)))
          (Relation.EqvGen.rel _ _ hXeF)
      · have hfx : (ecpUMap G x₀).face (.icp x) = .icp (G.face x) := ite_eq_right hx
        exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr hfx.symm))
  refine Hypermap.connected_of_forall_eqvGen _ .X fun u => ?_
  cases u with
  | X => exact Relation.EqvGen.refl _
  | Xe => exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hXXe)
  | icp x =>
    have h1 : Relation.EqvGen (ecpUMap G x₀).GLink (.icp x) (.icp (G.node (G.node x₀))) :=
      eqvGen_map EcpDart.icp key (Hypermap.eqvGen_glink_of_connected h x (G.node (G.node x₀)))
    refine Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ ?_)
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hXXe)
      (Relation.EqvGen.rel _ _ hXeN)

/-! #### Planarity of a `U` step -/

/-- A `U` step adds one face. -/
theorem cycleCount_face_ecpU :
    cycleCount (ecpUMap G x₀).face = cycleCount G.face + 1 := by
  have _ : Fintype (EcpDart D) := Fintype.ofFinite _
  have h1 : cycleCount (Equiv.swap (.Xe : EcpDart D) (.icp (G.node x₀))
      * EcpDart.extend G.face) + 1 = cycleCount (EcpDart.extend G.face) :=
    cycleCount_swap_mul_of_not_sameCycle _ (by simp) (not_sameCycle_extend_ecpU G x₀)
  rw [EcpDart.cycleCount_extend] at h1
  rw [ecpUMap_face_eq]
  omega

omit [DecidableEq D] in
/-- The geometrical hypotheses of the Euler formula, for the reversed ring. -/
private theorem ucyclePlainQuasicubicConnected_of (hplain : G.Plain)
    (hcubic : G.Quasicubic (G.cpring x₀)) (hconn : G.Connected) :
    G.UcyclePlainQuasicubicConnected (G.cpring x₀).reverse :=
  ⟨⟨⟨hplain, Hypermap.quasicubic_reverse hcubic⟩, isCyclicChain_reverse_cpring,
    List.nodup_reverse.mpr nodup_cpring⟩, hconn⟩

omit [DecidableEq D] in
/-- The reversed ring is nonempty. -/
private theorem reverse_cpring_ne_nil : (G.cpring x₀).reverse ≠ [] := by
  simpa using cpring_ne_nil (G := G) (x₀ := x₀)

/-- A `U` step preserves planarity. -/
theorem planar_ecpU (hplain : G.Plain) (hcubic : G.Quasicubic (G.cpring x₀))
    (hconn : G.Connected) (hplanar : G.Planar) : (ecpUMap G x₀).Planar := by
  have hEG := (quasicubic_Euler (ucyclePlainQuasicubicConnected_of G x₀ hplain hcubic hconn)
    (reverse_cpring_ne_nil G x₀)).mp hplanar
  rw [List.length_reverse] at hEG
  refine (quasicubic_Euler (ucyclePlainQuasicubicConnected_of (ecpUMap G x₀) .X
    (plain_ecpU G x₀ hplain) (quasicubic_ecpU G x₀ hcubic) (connected_ecpU G x₀ hconn))
    (reverse_cpring_ne_nil _ _)).mpr ?_
  rw [List.length_reverse, length_cpring_ecpU, cycleCount_face_ecpU, EcpDart.card_eq]
  omega

end EcpU

end Hypermap

/-! ### The N step: closing off a face -/

namespace Hypermap

section EcpN

variable [Finite D] [DecidableEq D] (G : Hypermap D) (x₀ : D)

omit [Finite D] [DecidableEq D] in
/-- Iterating `node` returns to `x₀` exactly at the multiples of the node
size. -/
theorem pow_node_eq_self_iff (k : ℕ) :
    (G.node ^ k) x₀ = x₀ ↔ Function.minimalPeriod G.node x₀ ∣ k := by
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
  constructor
  · intro h
    change G.node^[k] x₀ = x₀
    rwa [Perm.iterate_eq_pow]
  · intro h
    have hk : G.node^[k] x₀ = x₀ := h
    rwa [Perm.iterate_eq_pow] at hk

/-- The node map of an `N` step. -/
def ecpNNode : EcpDart D → EcpDart D
  | .X => if G.node⁻¹ x₀ = G.node x₀ then .X else .icp (G.node x₀)
  | .Xe => .icp (G.node⁻¹ x₀)
  | .icp y => if y = x₀ then .Xe else if G.node (G.node y) = x₀ then .X else .icp (G.node y)

/-- The face map of an `N` step. -/
def ecpNFace : EcpDart D → EcpDart D
  | .X => .icp x₀
  | .Xe => if G.node⁻¹ x₀ = G.node x₀ then .X else .icp (G.node⁻¹ (G.node⁻¹ x₀))
  | .icp y =>
      if y = G.edge (G.node⁻¹ x₀) then .Xe
      else if y = G.edge (G.node x₀) then .X else .icp (G.face y)

omit [Finite D] in
theorem ecpNNode_X : ecpNNode G x₀ .X =
    if G.node⁻¹ x₀ = G.node x₀ then .X else .icp (G.node x₀) := rfl

omit [Finite D] in
@[simp] theorem ecpNNode_Xe : ecpNNode G x₀ .Xe = .icp (G.node⁻¹ x₀) := rfl

omit [Finite D] in
theorem ecpNNode_icp (y : D) : ecpNNode G x₀ (.icp y) =
    if y = x₀ then .Xe else if G.node (G.node y) = x₀ then .X else .icp (G.node y) := rfl

omit [Finite D] in
@[simp] theorem ecpNFace_X : ecpNFace G x₀ .X = .icp x₀ := rfl

omit [Finite D] in
theorem ecpNFace_Xe : ecpNFace G x₀ .Xe =
    if G.node⁻¹ x₀ = G.node x₀ then .X else .icp (G.node⁻¹ (G.node⁻¹ x₀)) := rfl

omit [Finite D] in
theorem ecpNFace_icp (y : D) : ecpNFace G x₀ (.icp y) =
    if y = G.edge (G.node⁻¹ x₀) then .Xe
    else if y = G.edge (G.node x₀) then .X else .icp (G.face y) := rfl

omit [Finite D] in
/-- The three maps of an `N` step satisfy the hypermap identity. -/
theorem ecpN_cancel3 (u : EcpDart D) : ecpNNode G x₀ (ecpNFace G x₀ (ecpEdge G u)) = u := by
  cases u with
  | X =>
    rw [show ecpEdge G (.X) = (.Xe : EcpDart D) from rfl, ecpNFace_Xe]
    by_cases hl : G.node⁻¹ x₀ = G.node x₀
    · rw [ite_eq_left hl, ecpNNode_X, ite_eq_left hl]
    · rw [ite_eq_right hl, ecpNNode_icp]
      have h1 : G.node⁻¹ (G.node⁻¹ x₀) ≠ x₀ := by
        intro hc
        refine hl ?_
        have hd := congrArg (fun z => G.node z) hc
        simpa only [node_inv_node] using hd
      have h2 : G.node (G.node (G.node⁻¹ (G.node⁻¹ x₀))) = x₀ := by
        simp only [node_inv_node]
      rw [ite_eq_right h1, ite_eq_left h2]
  | Xe =>
    rw [show ecpEdge G (.Xe) = (.X : EcpDart D) from rfl, ecpNFace_X, ecpNNode_icp, ite_eq_left rfl]
  | icp x =>
    rw [show ecpEdge G (.icp x) = (.icp (G.edge x) : EcpDart D) from rfl, ecpNFace_icp]
    by_cases hA : G.edge x = G.edge (G.node⁻¹ x₀)
    · have hx : x = G.node⁻¹ x₀ := G.edge.injective hA
      rw [ite_eq_left hA, ecpNNode_Xe, hx]
    · rw [ite_eq_right hA]
      by_cases hB : G.edge x = G.edge (G.node x₀)
      · have hx : x = G.node x₀ := G.edge.injective hB
        have hne : G.node⁻¹ x₀ ≠ G.node x₀ := fun hc => hA (by rw [hB, hc])
        rw [ite_eq_left hB, ecpNNode_X, ite_eq_right hne, hx]
      · rw [ite_eq_right hB, G.face_edge x, ecpNNode_icp]
        have h1 : G.node⁻¹ x ≠ x₀ := by
          intro hc
          refine hB ?_
          have hd := congrArg (fun z => G.node z) hc
          simp only [node_inv_node] at hd
          rw [hd]
        have h2 : G.node (G.node (G.node⁻¹ x)) ≠ x₀ := by
          simp only [node_inv_node]
          intro hc
          refine hA ?_
          have hx : x = G.node⁻¹ x₀ := by rw [← hc, inv_node_node]
          rw [hx]
        rw [ite_eq_right h1, ite_eq_right h2]
        simp only [node_inv_node]

/-- The hypermap obtained by an `N` step at `x₀`. -/
noncomputable def ecpNMap : Hypermap (EcpDart D) :=
  ofCancel3 (ecpEdge G) (ecpNNode G x₀) (ecpNFace G x₀) (ecpN_cancel3 G x₀)

@[simp] theorem ecpNMap_edge (u : EcpDart D) : (ecpNMap G x₀).edge u = ecpEdge G u := rfl
@[simp] theorem ecpNMap_node (u : EcpDart D) : (ecpNMap G x₀).node u = ecpNNode G x₀ u := rfl
@[simp] theorem ecpNMap_face (u : EcpDart D) : (ecpNMap G x₀).face u = ecpNFace G x₀ u := rfl

/-- An `N` step preserves plainness. -/
theorem plain_ecpN (h : G.Plain) : (ecpNMap G x₀).Plain := by
  constructor
  · intro u
    cases u with
    | X => rfl
    | Xe => rfl
    | icp x => change (EcpDart.icp (G.edge (G.edge x)) : EcpDart D) = _; rw [h.edge_edge]
  · intro u
    cases u with
    | X => exact fun hu => by cases hu
    | Xe => exact fun hu => by cases hu
    | icp x => exact fun hu => h.edge_ne x (EcpDart.icp_injective hu)

/-- The ring after an `N` step at a dart with a trivial ring. -/
theorem cpring_ecpN_of_not_long (h : ¬ G.LongCpring x₀) :
    (ecpNMap G x₀).cpring .X = [.X] := by
  have hl : G.node⁻¹ x₀ = G.node x₀ := by
    rw [← G.face_edge x₀]
    exact not_not.mp h
  have hnode : (ecpNMap G x₀).node .X = .X := by
    rw [ecpNMap_node, ecpNNode_X, ite_eq_left hl]
  refine cpring_eq ?_ (by simp) (by simp) ?_
  · rw [isCyclicChain_singleton, hnode]
  · rw [hnode]; rfl

/-- The ring after an `N` step at a dart with a long ring. -/
theorem cpring_ecpN_of_long (h : G.LongCpring x₀) :
    (ecpNMap G x₀).cpring .X
      = .icp (G.node x₀) :: .X :: ((G.cpring x₀).drop 3).map EcpDart.icp := by
  obtain ⟨d, hd⟩ : ∃ d, (G.cpring x₀).drop 3 = d := ⟨_, rfl⟩
  rw [hd]
  have hlne : G.node⁻¹ x₀ ≠ G.node x₀ := by rw [← G.face_edge x₀]; exact h
  have hc3 : G.cpring x₀ = G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d := by
    rw [← hd, ← G.face_edge x₀]
    exact head_long_cpring h
  have hnd : (G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d).Nodup := hc3 ▸ nodup_cpring
  have hchain : List.IsChain (fun u v => u = G.node v)
      (G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d) := hc3 ▸ isCyclicChain_cpring.isChain
  have hnode : (ecpNMap G x₀).node .X = .icp (G.node x₀) := by
    rw [ecpNMap_node, ecpNNode_X, ite_eq_right hlne]
  have hlen : Function.minimalPeriod G.node x₀ = 3 + d.length := by
    rw [← length_cpring, hc3]
    simp only [List.length_cons]
    omega
  have hprop : G.node x₀ ≠ x₀ := (h.properCpring).symm
  have hx₀d : x₀ ∉ d := fun hc =>
    (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [hc])
  have hinvd : G.node⁻¹ x₀ ∉ d :=
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
  refine cpring_eq ?_ ?_ (by simp) (by rw [hnode]; rfl)
  · constructor
    · rw [List.isChain_cons_cons]
      refine ⟨hnode.symm, ?_⟩
      rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_map] at hy
        obtain ⟨d0, hd0, rfl⟩ := Option.mem_map.mp hy
        have hd0mem : d0 ∈ d := List.mem_of_mem_head? hd0
        have hlink : G.node⁻¹ x₀ = G.node d0 :=
          (List.isChain_cons.mp hchain.tail.tail).1 d0 hd0
        have hne0 : d0 ≠ x₀ := fun hc => hx₀d (hc ▸ hd0mem)
        have heq0 : G.node (G.node d0) = x₀ := by rw [← hlink, node_inv_node]
        rw [ecpNMap_node, ecpNNode_icp, ite_eq_right hne0, ite_eq_left heq0]
      · rw [List.isChain_map]
        refine (hchain.tail.tail.tail).imp_of_mem_tail_imp ?_
        intro a b ha hb hab
        have hbx : b ≠ x₀ := fun hc => hx₀d (hc ▸ List.mem_of_mem_tail hb)
        have hba : G.node (G.node b) ≠ x₀ := by
          rw [← hab]
          intro hc
          have hax : a = G.node⁻¹ x₀ := by rw [← hc, inv_node_node]
          exact hinvd (hax ▸ ha)
        change (EcpDart.icp a : EcpDart D) = ecpNNode G x₀ (.icp b)
        rw [ecpNNode_icp, ite_eq_right hbx, ite_eq_right hba, hab]
    · intro a ha b hb
      obtain rfl : b = EcpDart.icp (G.node x₀) := (Option.some.injEq _ _).mp hb.symm
      cases d with
      | nil =>
        simp only [List.map_nil, List.getLast?_cons_cons, List.getLast?_singleton,
          Option.mem_def, Option.some.injEq] at ha
        subst ha
        have h3 : G.node (G.node (G.node x₀)) = x₀ := by
          have hdvd : Function.minimalPeriod G.node x₀ ∣ 3 := by rw [hlen]; simp
          have h3' := (pow_node_eq_self_iff G x₀ 3).mpr hdvd
          simpa [pow_succ, Perm.mul_apply] using h3'
        rw [ecpNMap_node, ecpNNode_icp, ite_eq_right hprop, ite_eq_left h3]
      | cons d0 d' =>
        simp only [List.map_cons, List.getLast?_cons_cons] at ha
        rw [← List.map_cons, getLast?_map] at ha
        obtain ⟨c, hc, rfl⟩ := Option.mem_map.mp ha
        have hlastc : c = G.node (G.node x₀) := by
          have hlastring : (G.cpring x₀).getLast? = some c := by
            rw [hc3]
            simp only [List.getLast?_cons_cons]
            exact hc
          have hhead : (G.cpring x₀).head? = some (G.node x₀) := by rw [hc3]; rfl
          exact isCyclicChain_cpring.2 c hlastring (G.node x₀) hhead
        have h3 : G.node (G.node (G.node x₀)) ≠ x₀ := by
          intro hcc
          have hdvd : Function.minimalPeriod G.node x₀ ∣ 3 :=
            (pow_node_eq_self_iff G x₀ 3).mp (by simpa [pow_succ, Perm.mul_apply] using hcc)
          have hle := Nat.le_of_dvd (by norm_num) hdvd
          rw [hlen] at hle
          simp only [List.length_cons] at hle
          omega
        rw [ecpNMap_node, ecpNNode_icp, ite_eq_right hprop, ite_eq_right h3, hlastc]
  · rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with hcc | hcc
      · exact absurd hcc (by simp)
      · obtain ⟨y, hy, hyy⟩ := List.mem_map.mp hcc
        obtain rfl : y = G.node x₀ := EcpDart.icp_injective hyy
        exact (List.nodup_cons.mp hnd).1 (by simp [hy])
    · simp
    · exact ((List.nodup_cons.mp (List.nodup_cons.mp
        (List.nodup_cons.mp hnd).2).2).2).map EcpDart.icp_injective

/-- An `N` step with a long ring removes one dart from the ring. -/
theorem length_cpring_ecpN_of_long (h : G.LongCpring x₀) :
    ((ecpNMap G x₀).cpring .X).length = (G.cpring x₀).length - 1 := by
  have hlen : 2 < (G.cpring x₀).length := long_cpring_iff.mp h
  rw [cpring_ecpN_of_long G x₀ h]
  simp
  omega

/-- The ring after an `N` step at a long ring is nontrivial. -/
theorem properCpring_ecpN_of_long (h : G.LongCpring x₀) :
    (ecpNMap G x₀).ProperCpring .X := by
  refine proper_cpring_iff.mpr ?_
  rw [length_cpring_ecpN_of_long G x₀ h]
  have := long_cpring_iff.mp h
  omega

/-- The ring after an `N` step is long when the old ring had more than three
darts. -/
theorem longCpring_ecpN_of_long (h : G.LongCpring x₀)
    (hlen : 3 < (G.cpring x₀).length) : (ecpNMap G x₀).LongCpring .X := by
  refine long_cpring_iff.mpr ?_
  rw [length_cpring_ecpN_of_long G x₀ h]
  omega

/-- An `N` step at a long ring preserves quasicubicity. -/
theorem quasicubic_ecpN_of_long (hlong : G.LongCpring x₀) (h : G.Quasicubic (G.cpring x₀)) :
    (ecpNMap G x₀).Quasicubic ((ecpNMap G x₀).cpring .X) := by
  have hprop : x₀ ≠ G.node x₀ := hlong.properCpring
  have hinv : G.node⁻¹ x₀ ≠ x₀ := by
    intro hc
    refine hprop ?_
    have hd := congrArg (fun z => G.node z) hc
    simpa only [node_inv_node] using hd
  have hnodeXe : (ecpNMap G x₀).node .Xe = .icp (G.node⁻¹ x₀) := rfl
  have hnodeI : (ecpNMap G x₀).node (.icp (G.node⁻¹ x₀)) = .icp x₀ := by
    have hc : G.node (G.node (G.node⁻¹ x₀)) ≠ x₀ := by
      rw [node_inv_node]
      exact fun hcc => hprop hcc.symm
    rw [ecpNMap_node, ecpNNode_icp, ite_eq_right hinv, ite_eq_right hc, node_inv_node]
  have hnode0 : (ecpNMap G x₀).node (.icp x₀) = .Xe := by
    rw [ecpNMap_node, ecpNNode_icp, ite_eq_left rfl]
  have hgen : ∀ x : D, x ∉ G.cpring x₀ →
      (ecpNMap G x₀).node (.icp x) = .icp (G.node x) := by
    intro x hx
    have h1 : x ≠ x₀ := fun hc => hx (by rw [hc]; exact self_mem_cpring)
    have h2 : G.node (G.node x) ≠ x₀ := fun hc => hx (mem_cpring_of_node2 hc)
    rw [ecpNMap_node, ecpNNode_icp, ite_eq_right h1, ite_eq_right h2]
  have hclosed : ∀ x : D, x ∉ G.cpring x₀ → G.node x ∉ G.cpring x₀ :=
    fun x hx hc => hx (mem_cpring_node_iff.mp hc)
  have key : ∀ u : EcpDart D, u ∉ (ecpNMap G x₀).cpring EcpDart.X →
      u = .Xe ∨ u = .icp x₀ ∨ u = .icp (G.node⁻¹ x₀) ∨
        ∃ x : D, u = .icp x ∧ x ∉ G.cpring x₀ := by
    intro u hu
    rw [cpring_ecpN_of_long G x₀ hlong] at hu
    have hc3 : G.cpring x₀ = G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: (G.cpring x₀).drop 3 := by
      rw [← G.face_edge x₀]; exact head_long_cpring hlong
    cases u with
    | X => exact absurd (by simp) hu
    | Xe => exact Or.inl rfl
    | icp x =>
      by_cases h0 : x = x₀
      · exact Or.inr (Or.inl (by rw [h0]))
      by_cases h1 : x = G.node⁻¹ x₀
      · exact Or.inr (Or.inr (Or.inl (by rw [h1])))
      refine Or.inr (Or.inr (Or.inr ⟨x, rfl, fun hx => hu ?_⟩))
      rw [hc3] at hx
      rcases List.mem_cons.mp hx with hc | hx
      · exact List.mem_cons.mpr (Or.inl (by rw [hc]))
      rcases List.mem_cons.mp hx with hc | hx
      · exact absurd hc h0
      rcases List.mem_cons.mp hx with hc | hx
      · exact absurd hc h1
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
          (List.mem_map.mpr ⟨x, hx, rfl⟩))))
  constructor
  · intro u hu
    rcases key u hu with rfl | rfl | rfl | ⟨x, rfl, hx⟩
    · rw [hnodeXe, hnodeI, hnode0]
    · rw [hnode0, hnodeXe, hnodeI]
    · rw [hnodeI, hnode0, hnodeXe]
    · rw [hgen x hx, hgen _ (hclosed x hx), hgen _ (hclosed _ (hclosed x hx)),
        h.node_node_node hx]
  · intro u hu
    rcases key u hu with rfl | rfl | rfl | ⟨x, rfl, hx⟩
    · rw [hnodeXe]; simp
    · rw [hnode0]; simp
    · rw [hnodeI]
      exact fun hc => hinv (EcpDart.icp_injective hc).symm
    · rw [hgen x hx]
      exact fun hc => h.node_ne hx (EcpDart.icp_injective hc)

/-- The node image of the new dart after an `N` step at a long ring. -/
theorem ecpNNode_X_of_long (h : G.LongCpring x₀) :
    (ecpNMap G x₀).node .X = .icp (G.node x₀) := by
  have hl : G.node⁻¹ x₀ ≠ G.node x₀ := by rw [← G.face_edge x₀]; exact h
  rw [ecpNMap_node, ecpNNode_X, ite_eq_right hl]

/-! #### Face orbits of an `N` step -/

omit [Finite D] [DecidableEq D] in
/-- A dart has a prescribed face image exactly when it is the prescribed
predecessor. -/
private theorem face_eq_iff (y z : D) : G.face y = z ↔ y = G.edge (G.node z) :=
  ⟨fun h => by rw [← h, G.faceK], fun h => by rw [h, G.nodeK]⟩

omit [Finite D] [DecidableEq D] in
/-- The `N` step degenerates exactly when the ring of `x₀` is not long. -/
private theorem inv_inv_node_eq_iff :
    G.node⁻¹ (G.node⁻¹ x₀) = x₀ ↔ G.node⁻¹ x₀ = G.node x₀ := by
  constructor
  · intro h
    have h' := congrArg G.node h
    rwa [node_inv_node] at h'
  · intro h
    rw [h, inv_node_node]

/-- The face map of an `N` step is the extended face map of `G` composed with
the two transpositions that splice `Xe` into the face of `node⁻¹ (node⁻¹ x₀)`
and `X` into the face of `x₀`. -/
theorem ecpNMap_face_eq :
    (ecpNMap G x₀).face
      = Equiv.swap .X (.icp x₀)
        * (Equiv.swap .Xe (.icp (G.node⁻¹ (G.node⁻¹ x₀))) * EcpDart.extend G.face) := by
  ext u
  rw [Perm.mul_apply, Perm.mul_apply]
  cases u with
  | X =>
    have e1 : EcpDart.extend G.face (.X : EcpDart D) = .X := rfl
    have e2 : Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀))) .X = .X :=
      Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
    have e3 : Equiv.swap (.X : EcpDart D) (.icp x₀) .X = .icp x₀ := Equiv.swap_apply_left _ _
    rw [e1, e2, e3]
    rfl
  | Xe =>
    have e1 : EcpDart.extend G.face (.Xe : EcpDart D) = .Xe := rfl
    have e2 : Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀))) .Xe
        = .icp (G.node⁻¹ (G.node⁻¹ x₀)) := Equiv.swap_apply_left _ _
    have hlhs : (ecpNMap G x₀).face .Xe
        = if G.node⁻¹ x₀ = G.node x₀ then .X else .icp (G.node⁻¹ (G.node⁻¹ x₀)) := rfl
    rw [e1, e2, hlhs]
    by_cases hd : G.node⁻¹ x₀ = G.node x₀
    · have hb : G.node⁻¹ (G.node⁻¹ x₀) = x₀ := (inv_inv_node_eq_iff G x₀).mpr hd
      have e3 : Equiv.swap (.X : EcpDart D) (.icp x₀) (.icp (G.node⁻¹ (G.node⁻¹ x₀))) = .X := by
        rw [hb]; exact Equiv.swap_apply_right _ _
      rw [ite_eq_left hd, e3]
    · have hb : G.node⁻¹ (G.node⁻¹ x₀) ≠ x₀ := fun hc => hd ((inv_inv_node_eq_iff G x₀).mp hc)
      have e3 : Equiv.swap (.X : EcpDart D) (.icp x₀) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
          = .icp (G.node⁻¹ (G.node⁻¹ x₀)) :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hb)
      rw [ite_eq_right hd, e3]
  | icp y =>
    have e1 : EcpDart.extend G.face (.icp y) = .icp (G.face y) := rfl
    have hlhs : (ecpNMap G x₀).face (.icp y)
        = if y = G.edge (G.node⁻¹ x₀) then .Xe
          else if y = G.edge (G.node x₀) then .X else .icp (G.face y) := rfl
    have hb : G.edge (G.node (G.node⁻¹ (G.node⁻¹ x₀))) = G.edge (G.node⁻¹ x₀) := by
      rw [node_inv_node]
    rw [e1, hlhs]
    by_cases h1 : y = G.edge (G.node⁻¹ x₀)
    · have hfy : G.face y = G.node⁻¹ (G.node⁻¹ x₀) := by
        rw [face_eq_iff, hb]; exact h1
      have e2 : Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
          (.icp (G.face y)) = .Xe := by rw [hfy]; exact Equiv.swap_apply_right _ _
      have e3 : Equiv.swap (.X : EcpDart D) (.icp x₀) .Xe = .Xe :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
      rw [ite_eq_left h1, e2, e3]
    · have hfy : G.face y ≠ G.node⁻¹ (G.node⁻¹ x₀) := by
        intro hc
        exact h1 (by rw [← hb, ← face_eq_iff]; exact hc)
      have e2 : Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
          (.icp (G.face y)) = .icp (G.face y) :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hfy)
      rw [ite_eq_right h1, e2]
      by_cases h2 : y = G.edge (G.node x₀)
      · have hfy2 : G.face y = x₀ := by rw [face_eq_iff]; exact h2
        have e3 : Equiv.swap (.X : EcpDart D) (.icp x₀) (.icp (G.face y)) = .X := by
          rw [hfy2]; exact Equiv.swap_apply_right _ _
        rw [ite_eq_left h2, e3]
      · have hfy2 : G.face y ≠ x₀ := fun hc => h2 ((face_eq_iff G y x₀).mp hc)
        have e3 : Equiv.swap (.X : EcpDart D) (.icp x₀) (.icp (G.face y)) = .icp (G.face y) :=
          Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hfy2)
        rw [ite_eq_right h2, e3]

/-- Splicing in the second new dart of an `N` step merges the orbit of `Xe` into
the face of `node⁻¹ (node⁻¹ x₀)`. -/
private theorem sameCycle_faceN_aux (u v : EcpDart D) :
    (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
        * EcpDart.extend G.face).SameCycle u v ↔
      (EcpDart.extend G.face).SameCycle u v
        ∨ ((EcpDart.extend G.face).SameCycle u .Xe
            ∧ (EcpDart.extend G.face).SameCycle v (.icp (G.node⁻¹ (G.node⁻¹ x₀))))
        ∨ ((EcpDart.extend G.face).SameCycle u (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
            ∧ (EcpDart.extend G.face).SameCycle v .Xe) :=
  sameCycle_swap_mul (by simp)
    (by rw [EcpDart.sameCycle_extend_Xe_left]; simp) u v

/-- The orbit of the first new dart of an `N` step is still a singleton after
the second new dart has been spliced in. -/
private theorem not_sameCycle_faceN_aux :
    ¬ (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
        * EcpDart.extend G.face).SameCycle (.X : EcpDart D) (.icp x₀) := by
  rw [sameCycle_faceN_aux]
  simp [EcpDart.sameCycle_extend_X_left]

/-- The face orbits of an `N` step. -/
theorem sameCycle_face_ecpN (u v : EcpDart D) :
    (ecpNMap G x₀).face.SameCycle u v ↔
      (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
            * EcpDart.extend G.face).SameCycle u v
        ∨ ((Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
              * EcpDart.extend G.face).SameCycle u .X
            ∧ (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
              * EcpDart.extend G.face).SameCycle v (.icp x₀))
        ∨ ((Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
              * EcpDart.extend G.face).SameCycle u (.icp x₀)
            ∧ (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
              * EcpDart.extend G.face).SameCycle v .X) := by
  rw [ecpNMap_face_eq]
  exact sameCycle_swap_mul (by simp) (not_sameCycle_faceN_aux G x₀) u v

/-- An `N` step does not change the face orbits of the old darts. -/
theorem cface_icpN (x y : D) :
    (ecpNMap G x₀).CFace (.icp x) (.icp y) ↔ G.CFace x y := by
  rw [show (ecpNMap G x₀).CFace (.icp x) (.icp y) ↔ _ from
    sameCycle_face_ecpN G x₀ (.icp x) (.icp y)]
  simp only [sameCycle_faceN_aux]
  simp [EcpDart.sameCycle_extend_icp,
    EcpDart.sameCycle_extend_Xe_right, EcpDart.sameCycle_extend_X_left,
    EcpDart.sameCycle_extend_X_right]

/-- The first new dart of an `N` step joins the face of `x₀`. -/
theorem cface_ecpN_icp (z : D) :
    (ecpNMap G x₀).CFace .X (.icp z) ↔ G.CFace z x₀ := by
  rw [show (ecpNMap G x₀).CFace .X (.icp z) ↔ _ from
    sameCycle_face_ecpN G x₀ .X (.icp z)]
  simp only [sameCycle_faceN_aux]
  simp [EcpDart.sameCycle_extend_icp,
    EcpDart.sameCycle_extend_Xe_right, EcpDart.sameCycle_extend_X_left,
    EcpDart.sameCycle_extend_X_right]

/-- The first new dart of an `N` step lies on the face of `x₀`. -/
theorem cface_ecpN : (ecpNMap G x₀).CFace .X (.icp x₀) :=
  (cface_ecpN_icp G x₀ x₀).mpr (SameCycle.refl _ _)

/-- The second new dart of an `N` step joins the face of `node⁻¹ (node⁻¹ x₀)`. -/
theorem cface_Xe_icpN (z : D) :
    (ecpNMap G x₀).CFace .Xe (.icp z) ↔ G.CFace z (G.node⁻¹ (G.node⁻¹ x₀)) := by
  rw [show (ecpNMap G x₀).CFace .Xe (.icp z) ↔ _ from
    sameCycle_face_ecpN G x₀ .Xe (.icp z)]
  simp only [sameCycle_faceN_aux]
  simp [EcpDart.sameCycle_extend_icp, EcpDart.sameCycle_extend_Xe_left,
    EcpDart.sameCycle_extend_Xe_right, EcpDart.sameCycle_extend_X_left,
    EcpDart.sameCycle_extend_X_right]

/-- Every dart of an `N` step map lies on the face of an old dart: an `N` step
adds no face. -/
theorem fband_icpN (u : EcpDart D) : ∃ x : D, (ecpNMap G x₀).CFace u (.icp x) := by
  cases u with
  | X => exact ⟨x₀, cface_ecpN G x₀⟩
  | Xe =>
    exact ⟨G.node⁻¹ (G.node⁻¹ x₀),
      (cface_Xe_icpN G x₀ _).mpr (SameCycle.refl _ _)⟩
  | icp x => exact ⟨x, SameCycle.refl _ _⟩

/-- Adjacency after an `N` step: the two faces closed off by the step become
adjacent to each other. -/
theorem adj_icpN (x y : D) :
    (ecpNMap G x₀).Adj (.icp x) (.icp y) ↔
      G.Adj x y ∨ (G.CFace x (G.node⁻¹ (G.node⁻¹ x₀)) ∧ G.CFace y x₀)
        ∨ (G.CFace x x₀ ∧ G.CFace y (G.node⁻¹ (G.node⁻¹ x₀))) := by
  have hedgeX : (ecpNMap G x₀).edge .X = .Xe := rfl
  have hedgeXe : (ecpNMap G x₀).edge .Xe = .X := rfl
  constructor
  · rintro ⟨u, hu, hru⟩
    cases u with
    | X =>
      rw [Rlink, hedgeX] at hru
      exact Or.inr (Or.inr ⟨(cface_ecpN_icp G x₀ x).mp hu.symm,
        (cface_Xe_icpN G x₀ y).mp hru⟩)
    | Xe =>
      rw [Rlink, hedgeXe] at hru
      exact Or.inr (Or.inl ⟨(cface_Xe_icpN G x₀ x).mp hu.symm,
        (cface_ecpN_icp G x₀ y).mp hru⟩)
    | icp z =>
      have hedge : (ecpNMap G x₀).edge (.icp z) = .icp (G.edge z) := rfl
      rw [Rlink, hedge] at hru
      exact Or.inl ⟨z, (cface_icpN G x₀ x z).mp hu, (cface_icpN G x₀ _ y).mp hru⟩
  · rintro (⟨z, hz, hrz⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨.icp z, (cface_icpN G x₀ x z).mpr hz, ?_⟩
      have hedge : (ecpNMap G x₀).edge (.icp z) = .icp (G.edge z) := rfl
      rw [Rlink, hedge]
      exact (cface_icpN G x₀ _ y).mpr hrz
    · refine ⟨.Xe, ((cface_Xe_icpN G x₀ x).mpr h1).symm, ?_⟩
      rw [Rlink, hedgeXe]
      exact (cface_ecpN_icp G x₀ y).mpr h2
    · refine ⟨.X, ((cface_ecpN_icp G x₀ x).mpr h1).symm, ?_⟩
      rw [Rlink, hedgeX]
      exact (cface_Xe_icpN G x₀ y).mpr h2

/-- An `N` step preserves adjacency of old darts. -/
theorem sub_adj_icpN {x y : D} (h : G.Adj x y) :
    (ecpNMap G x₀).Adj (.icp x) (.icp y) := (adj_icpN G x₀ x y).mpr (Or.inl h)

/-- The two new darts of an `N` step share a face exactly when the new edge is a
bridge. -/
theorem cface_ecpN_Xe :
    (ecpNMap G x₀).CFace .X .Xe ↔ G.CFace x₀ (G.node⁻¹ (G.node⁻¹ x₀)) := by
  rw [show (ecpNMap G x₀).CFace .X .Xe ↔ _ from sameCycle_face_ecpN G x₀ .X .Xe]
  simp only [sameCycle_faceN_aux]
  simp [EcpDart.sameCycle_extend_icp, EcpDart.sameCycle_extend_Xe_left,
    EcpDart.sameCycle_extend_Xe_right, EcpDart.sameCycle_extend_X_left,
    EcpDart.sameCycle_extend_X_right]

/-- An `N` step preserves bridgelessness as soon as the new edge is not a
bridge. -/
theorem bridgeless_ecpN (h : G.Bridgeless)
    (hX : ¬ G.CFace x₀ (G.node⁻¹ (G.node⁻¹ x₀))) : (ecpNMap G x₀).Bridgeless := by
  intro u hu
  cases u with
  | X =>
    have hedge : (ecpNMap G x₀).edge .X = .Xe := rfl
    rw [hedge] at hu
    exact hX ((cface_ecpN_Xe G x₀).mp hu)
  | Xe =>
    have hedge : (ecpNMap G x₀).edge .Xe = .X := rfl
    rw [hedge] at hu
    exact hX ((cface_ecpN_Xe G x₀).mp hu.symm)
  | icp x =>
    have hedge : (ecpNMap G x₀).edge (.icp x) = .icp (G.edge x) := rfl
    rw [hedge] at hu
    exact h x ((cface_icpN G x₀ x (G.edge x)).mp hu)

/-- The dart just before the new dart in the node cycle of an `N` step lies on
the face of `node⁻¹ (node⁻¹ x₀)`. -/
theorem cface_inv_node_ecpN :
    (ecpNMap G x₀).CFace ((ecpNMap G x₀).node⁻¹ .X)
      (.icp (G.node⁻¹ (G.node⁻¹ x₀))) := by
  by_cases hd : G.node⁻¹ x₀ = G.node x₀
  · have hnX : (ecpNMap G x₀).node .X = .X := by
      rw [ecpNMap_node, ecpNNode_X, ite_eq_left hd]
    have hinv : (ecpNMap G x₀).node⁻¹ (.X : EcpDart D) = .X :=
      Equiv.Perm.inv_eq_iff_eq.mpr hnX.symm
    have hb : G.node⁻¹ (G.node⁻¹ x₀) = x₀ := (inv_inv_node_eq_iff G x₀).mpr hd
    rw [hinv, hb, cface_ecpN_icp]
  · have hne : G.node⁻¹ (G.node⁻¹ x₀) ≠ x₀ := fun hc =>
      hd ((inv_inv_node_eq_iff G x₀).mp hc)
    have hnn : G.node (G.node (G.node⁻¹ (G.node⁻¹ x₀))) = x₀ := by
      rw [node_inv_node, node_inv_node]
    have hstep : (ecpNMap G x₀).node (.icp (G.node⁻¹ (G.node⁻¹ x₀))) = .X := by
      rw [ecpNMap_node, ecpNNode_icp, ite_eq_right hne, ite_eq_left hnn]
    have hinv : (ecpNMap G x₀).node⁻¹ (.X : EcpDart D)
        = .icp (G.node⁻¹ (G.node⁻¹ x₀)) := Equiv.Perm.inv_eq_iff_eq.mpr hstep.symm
    rw [hinv]

/-- **The ring of a `K` step**: it is the ring of `x₀` with its first two darts
replaced by the new dart. -/
theorem cpring_ecpK (h : G.ProperCpring x₀) :
    (ecpNMap G (G.node x₀)).cpring ((ecpNMap G (G.node x₀)).node⁻¹ .X)
      = .X :: ((G.cpring x₀).drop 2).map EcpDart.icp := by
  have hnode : (ecpNMap G (G.node x₀)).node ((ecpNMap G (G.node x₀)).node⁻¹ .X) = .X :=
    node_inv_node _ _
  have hnd2 : ((G.cpring x₀).drop 2).Nodup := by
    have hn := nodup_cpring (G := G) (x₀ := x₀)
    rw [← List.take_append_drop 2 (G.cpring x₀)] at hn
    exact hn.of_append_right
  have hndL : ((.X : EcpDart D) :: ((G.cpring x₀).drop 2).map EcpDart.icp).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, hnd2.map EcpDart.icp_injective⟩
    intro hc
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hc
    exact absurd hw (by simp)
  by_cases hl : G.LongCpring x₀
  · obtain ⟨d, hd⟩ : ∃ d, (G.cpring x₀).drop 3 = d := ⟨_, rfl⟩
    have hc3 : G.cpring x₀ = G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d := by
      rw [← hd, ← G.face_edge x₀]
      exact head_long_cpring hl
    have hdrop : (G.cpring x₀).drop 2 = G.node⁻¹ x₀ :: d := by rw [hc3]; rfl
    have hne' : G.node⁻¹ x₀ ≠ G.node x₀ := by rw [← G.face_edge x₀]; exact hl
    have hl' : G.LongCpring (G.node x₀) := by
      intro hc
      rw [G.face_edge, inv_node_node] at hc
      refine hne' ?_
      conv_lhs => rw [hc]
      rw [inv_node_node]
    have hNX : (ecpNMap G (G.node x₀)).node .X = .icp (G.node (G.node x₀)) :=
      ecpNNode_X_of_long G (G.node x₀) hl'
    have hnd : (G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d).Nodup := hc3 ▸ nodup_cpring
    have hchain : List.IsChain (fun u v => u = G.node v)
        (G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d) := hc3 ▸ isCyclicChain_cpring.isChain
    have hnx₀d : G.node x₀ ∉ d := fun hc => (List.nodup_cons.mp hnd).1 (by simp [hc])
    have hinvd : G.node⁻¹ x₀ ∉ d :=
      (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
    rw [hdrop] at hndL ⊢
    refine cpring_eq ?_ hndL (by simp) (by rw [hnode]; rfl)
    constructor
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_map] at hy
        obtain ⟨c, hc, rfl⟩ := Option.mem_map.mp hy
        obtain rfl : c = G.node⁻¹ x₀ := (Option.some.injEq _ _).mp hc.symm
        have hnn : G.node (G.node (G.node⁻¹ x₀)) = G.node x₀ := by rw [node_inv_node]
        change (EcpDart.X : EcpDart D) = ecpNNode G (G.node x₀) (.icp (G.node⁻¹ x₀))
        rw [ecpNNode_icp, ite_eq_right hne', ite_eq_left hnn]
      · rw [List.isChain_map]
        refine (hchain.tail.tail).imp_of_mem_tail_imp ?_
        intro a b _ hb hab
        have hb1 : b ≠ G.node x₀ := fun hc => hnx₀d (hc ▸ hb)
        have hb2 : G.node (G.node b) ≠ G.node x₀ := by
          intro hc
          have hbb : b = G.node⁻¹ x₀ := by
            have h1 : G.node b = x₀ := G.node.injective hc
            rw [← h1, inv_node_node]
          exact hinvd (hbb ▸ hb)
        change (EcpDart.icp a : EcpDart D) = ecpNNode G (G.node x₀) (.icp b)
        rw [ecpNNode_icp, ite_eq_right hb1, ite_eq_right hb2, hab]
    · intro a ha b hb
      obtain rfl : b = (EcpDart.X : EcpDart D) := (Option.some.injEq _ _).mp hb.symm
      rw [getLast?_cons_ne_nil (by simp), getLast?_map] at ha
      obtain ⟨c, hc, rfl⟩ := Option.mem_map.mp ha
      have hlastring : (G.cpring x₀).getLast? = some c := by
        rw [hc3, getLast?_cons_ne_nil (by simp), getLast?_cons_ne_nil (by simp)]
        exact hc
      have hhead : (G.cpring x₀).head? = some (G.node x₀) := by rw [hc3]; rfl
      have hlast : c = G.node (G.node x₀) :=
        isCyclicChain_cpring.2 c hlastring (G.node x₀) hhead
      rw [hlast]
      exact hNX.symm
  · have hlen : ¬ 2 < (G.cpring x₀).length := fun hc => hl (long_cpring_iff.mpr hc)
    have hlen2 : (G.cpring x₀).length = 2 := by
      have h1 := proper_cpring_iff.mp h
      omega
    have hdrop : (G.cpring x₀).drop 2 = [] := by
      rw [← List.length_eq_zero_iff, List.length_drop, hlen2]
    have hinv : G.node⁻¹ x₀ = G.node x₀ := by
      rw [← G.face_edge x₀]
      exact not_not.mp hl
    have hdeg : G.node⁻¹ (G.node x₀) = G.node (G.node x₀) := by
      rw [inv_node_node]
      have hc := congrArg G.node hinv
      rw [node_inv_node] at hc
      exact hc
    have hNX : (ecpNMap G (G.node x₀)).node .X = .X := by
      rw [ecpNMap_node, ecpNNode_X, ite_eq_left hdeg]
    rw [hdrop]
    refine cpring_eq ?_ (by simp) (by simp) (by rw [hnode]; rfl)
    rw [List.map_nil, isCyclicChain_singleton]
    exact hNX.symm

/-! #### Connectivity of an `N` step -/

/-- An `N` step preserves connectedness. -/
theorem connected_ecpN (h : G.Connected) : (ecpNMap G x₀).Connected := by
  have hXXe : (ecpNMap G x₀).GLink .X .Xe := Or.inl rfl
  have hXF : (ecpNMap G x₀).GLink .X (.icp x₀) := Or.inr (Or.inr rfl)
  have hXeN : (ecpNMap G x₀).GLink .Xe (.icp (G.node⁻¹ x₀)) := Or.inr (Or.inl rfl)
  have hXinv : Relation.EqvGen (ecpNMap G x₀).GLink (.X : EcpDart D) (.icp (G.node⁻¹ x₀)) :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hXXe)
      (Relation.EqvGen.rel _ _ hXeN)
  have hXnode : Relation.EqvGen (ecpNMap G x₀).GLink (.X : EcpDart D) (.icp (G.node x₀)) := by
    by_cases hd : G.node⁻¹ x₀ = G.node x₀
    · rw [← hd]; exact hXinv
    · have hn : (ecpNMap G x₀).node .X = .icp (G.node x₀) := by
        rw [ecpNMap_node, ecpNNode_X, ite_eq_right hd]
      exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl hn.symm))
  have hXeb : Relation.EqvGen (ecpNMap G x₀).GLink (.Xe : EcpDart D)
      (.icp (G.node⁻¹ (G.node⁻¹ x₀))) := by
    by_cases hd : G.node⁻¹ x₀ = G.node x₀
    · have hb : G.node⁻¹ (G.node⁻¹ x₀) = x₀ := (inv_inv_node_eq_iff G x₀).mpr hd
      have hf : (ecpNMap G x₀).face .Xe = .X := by
        rw [ecpNMap_face, ecpNFace_Xe, ite_eq_left hd]
      rw [hb]
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.rel _ _ (Or.inr (Or.inr hf.symm)))
        (Relation.EqvGen.rel _ _ hXF)
    · have hf : (ecpNMap G x₀).face .Xe = .icp (G.node⁻¹ (G.node⁻¹ x₀)) := by
        rw [ecpNMap_face, ecpNFace_Xe, ite_eq_right hd]
      exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr hf.symm))
  have key : ∀ x y : D, G.GLink x y →
      Relation.EqvGen (ecpNMap G x₀).GLink (.icp x) (.icp y) := by
    intro x y hxy
    rcases hxy with rfl | rfl | rfl
    · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
    · by_cases h0 : x = x₀
      · have hn : (ecpNMap G x₀).node (.icp x) = .Xe := by
          rw [ecpNMap_node, ecpNNode_icp, ite_eq_left h0]
        have hnx : G.node x = G.node x₀ := by rw [h0]
        rw [hnx]
        refine Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ (Or.inr (Or.inl hn.symm))) ?_
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hXXe)) hXnode
      · by_cases h1 : G.node (G.node x) = x₀
        · have hn : (ecpNMap G x₀).node (.icp x) = .X := by
            rw [ecpNMap_node, ecpNNode_icp, ite_eq_right h0, ite_eq_left h1]
          have hnx : G.node x = G.node⁻¹ x₀ := by rw [← h1, inv_node_node]
          rw [hnx]
          exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.rel _ _ (Or.inr (Or.inl hn.symm))) hXinv
        · have hn : (ecpNMap G x₀).node (.icp x) = .icp (G.node x) := by
            rw [ecpNMap_node, ecpNNode_icp, ite_eq_right h0, ite_eq_right h1]
          exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl hn.symm))
    · by_cases h0 : x = G.edge (G.node⁻¹ x₀)
      · have hf : (ecpNMap G x₀).face (.icp x) = .Xe := by
          rw [ecpNMap_face, ecpNFace_icp, ite_eq_left h0]
        have hfx : G.face x = G.node⁻¹ (G.node⁻¹ x₀) := by rw [h0, G.face_edge]
        rw [hfx]
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ (Or.inr (Or.inr hf.symm))) hXeb
      · by_cases h1 : x = G.edge (G.node x₀)
        · have hf : (ecpNMap G x₀).face (.icp x) = .X := by
            rw [ecpNMap_face, ecpNFace_icp, ite_eq_right h0, ite_eq_left h1]
          have hfx : G.face x = x₀ := by rw [h1, G.nodeK]
          rw [hfx]
          exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.rel _ _ (Or.inr (Or.inr hf.symm)))
            (Relation.EqvGen.rel _ _ hXF)
        · have hf : (ecpNMap G x₀).face (.icp x) = .icp (G.face x) := by
            rw [ecpNMap_face, ecpNFace_icp, ite_eq_right h0, ite_eq_right h1]
          exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr hf.symm))
  refine Hypermap.connected_of_forall_eqvGen _ .X fun u => ?_
  cases u with
  | X => exact Relation.EqvGen.refl _
  | Xe => exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hXXe)
  | icp x =>
    have h1 : Relation.EqvGen (ecpNMap G x₀).GLink (.icp x) (.icp x₀) :=
      eqvGen_map EcpDart.icp key (Hypermap.eqvGen_glink_of_connected h x x₀)
    exact Relation.EqvGen.trans _ _ _ h1
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hXF))

/-! #### Planarity of an `N` step -/

/-- An `N` step adds no face. -/
theorem cycleCount_face_ecpN :
    cycleCount (ecpNMap G x₀).face = cycleCount G.face := by
  have _ : Fintype (EcpDart D) := Fintype.ofFinite _
  have h1 : cycleCount (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
      * EcpDart.extend G.face) + 1 = cycleCount (EcpDart.extend G.face) :=
    cycleCount_swap_mul_of_not_sameCycle _ (by simp)
      (by rw [EcpDart.sameCycle_extend_Xe_left]; simp)
  have h2 : cycleCount (Equiv.swap (.X : EcpDart D) (.icp x₀)
      * (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
        * EcpDart.extend G.face)) + 1
      = cycleCount (Equiv.swap (.Xe : EcpDart D) (.icp (G.node⁻¹ (G.node⁻¹ x₀)))
        * EcpDart.extend G.face) :=
    cycleCount_swap_mul_of_not_sameCycle _ (by simp) (not_sameCycle_faceN_aux G x₀)
  rw [EcpDart.cycleCount_extend] at h1
  rw [ecpNMap_face_eq]
  omega

/-- An `N` step at a long ring preserves planarity. -/
theorem planar_ecpN (hlong : G.LongCpring x₀) (hplain : G.Plain)
    (hcubic : G.Quasicubic (G.cpring x₀)) (hconn : G.Connected) (hplanar : G.Planar) :
    (ecpNMap G x₀).Planar := by
  have hlen : 2 < (G.cpring x₀).length := long_cpring_iff.mp hlong
  have hEG := (quasicubic_Euler (ucyclePlainQuasicubicConnected_of G x₀ hplain hcubic hconn)
    (reverse_cpring_ne_nil G x₀)).mp hplanar
  rw [List.length_reverse] at hEG
  refine (quasicubic_Euler (ucyclePlainQuasicubicConnected_of (ecpNMap G x₀) .X
    (plain_ecpN G x₀ hplain) (quasicubic_ecpN_of_long G x₀ hlong hcubic)
    (connected_ecpN G x₀ hconn)) (reverse_cpring_ne_nil _ _)).mpr ?_
  rw [List.length_reverse, length_cpring_ecpN_of_long G x₀ hlong, cycleCount_face_ecpN,
    EcpDart.card_eq]
  omega

end EcpN

/-! ### The composite `Y` and `H` steps

A `Y` step is a `U` step followed by an `N` step, and an `H` step is a `Y` step
followed by an `N` step; these lemmas record how the ring and the node map of
the composites act on the old darts. -/

section EcpComposite

variable [Finite D] [DecidableEq D] (G : Hypermap D) (x₀ : D)

/-- The ring after a `U` step, on old darts. -/
theorem mem_cpring_ecpU_icp {x : D} :
    (.icp x : EcpDart D) ∈ (ecpUMap G x₀).cpring .X ↔ x ∈ G.cpring x₀ := by
  rw [cpring_ecpU]
  simp

/-- The node image of the new dart after a `Y` step. -/
theorem node_ecpY_X :
    (ecpNMap (ecpUMap G x₀) .X).node .X = .icp (.Xe : EcpDart D) :=
  ecpNNode_X_of_long (ecpUMap G x₀) .X (longCpring_ecpU G x₀)

/-- An old dart off the ring stays off the ring after a `Y` step. -/
theorem not_mem_cpring_ecpY {x : D} (hx : x ∉ G.cpring x₀) :
    (.icp (.icp x) : EcpDart (EcpDart D)) ∉ (ecpNMap (ecpUMap G x₀) .X).cpring .X := by
  rw [cpring_ecpN_of_long (ecpUMap G x₀) .X (longCpring_ecpU G x₀)]
  have hnX : (ecpUMap G x₀).node (.X : EcpDart D) = .Xe := rfl
  rw [hnX]
  simp only [List.mem_cons, List.mem_map, not_or]
  refine ⟨by simp, by simp, ?_⟩
  rintro ⟨v, hv, hveq⟩
  obtain rfl : v = .icp x := EcpDart.icp_inj.mp hveq
  exact hx ((mem_cpring_ecpU_icp G x₀).mp (List.mem_of_mem_drop hv))

/-- An old dart off the ring stays off the ring after an `H` step. -/
theorem not_mem_cpring_ecpH {x : D} (hx : x ∉ G.cpring x₀) :
    (.icp (.icp (.icp x)) : EcpDart (EcpDart (EcpDart D)))
      ∉ (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).cpring .X := by
  by_cases hl : (ecpNMap (ecpUMap G x₀) .X).LongCpring .X
  · rw [cpring_ecpN_of_long _ _ hl, node_ecpY_X]
    simp only [List.mem_cons, List.mem_map, not_or]
    refine ⟨by simp, by simp, ?_⟩
    rintro ⟨v, hv, hveq⟩
    obtain rfl : v = .icp (.icp x) := EcpDart.icp_inj.mp hveq
    exact not_mem_cpring_ecpY G x₀ hx (List.mem_of_mem_drop hv)
  · rw [cpring_ecpN_of_not_long _ _ hl]
    simp

/-- The node map of a `Y` step on old darts off the ring. -/
theorem node_ecpY_icp {x : D} (hx : x ∉ G.cpring x₀) :
    (ecpNMap (ecpUMap G x₀) .X).node (.icp (.icp x)) = .icp (.icp (G.node x)) := by
  have hx0 : x ≠ G.node x₀ := fun hc => hx (by rw [hc]; exact node_mem_cpring)
  have hx₀' : x ≠ x₀ := fun hc => hx (by rw [hc]; exact self_mem_cpring)
  have hnx : G.node x ≠ G.node x₀ := fun hc => hx₀' (G.node.injective hc)
  have e1 : (ecpUMap G x₀).node (.icp x) = .icp (G.node x) := ecpUNode_icp_of_ne G x₀ hx0
  have e2 : (ecpUMap G x₀).node (.icp (G.node x)) = .icp (G.node (G.node x)) :=
    ecpUNode_icp_of_ne G x₀ hnx
  have hne : (.icp x : EcpDart D) ≠ .X := by simp
  have hne2 : (ecpUMap G x₀).node ((ecpUMap G x₀).node (.icp x)) ≠ .X := by
    rw [e1, e2]; simp
  have hrw : (ecpNMap (ecpUMap G x₀) .X).node (.icp (.icp x))
      = if (.icp x : EcpDart D) = .X then (.Xe : EcpDart (EcpDart D))
        else if (ecpUMap G x₀).node ((ecpUMap G x₀).node (.icp x)) = .X then .X
          else .icp ((ecpUMap G x₀).node (.icp x)) := rfl
  rw [hrw, ite_eq_right hne, ite_eq_right hne2, e1]

/-- The node map of an `H` step on old darts off the ring. -/
theorem node_ecpH_icp {x : D} (hx : x ∉ G.cpring x₀) :
    (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).node (.icp (.icp (.icp x)))
      = .icp (.icp (.icp (G.node x))) := by
  have hnx : G.node x ∉ G.cpring x₀ := fun hc => hx (mem_cpring_node_iff.mp hc)
  have e1 := node_ecpY_icp G x₀ hx
  have e2 := node_ecpY_icp G x₀ hnx
  have hne : (.icp (.icp x) : EcpDart (EcpDart D)) ≠ .X := by simp
  have hne2 : (ecpNMap (ecpUMap G x₀) .X).node
      ((ecpNMap (ecpUMap G x₀) .X).node (.icp (.icp x))) ≠ .X := by
    rw [e1, e2]; simp
  have hrw : (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).node (.icp (.icp (.icp x)))
      = if (.icp (.icp x) : EcpDart (EcpDart D)) = .X then
          (.Xe : EcpDart (EcpDart (EcpDart D)))
        else if (ecpNMap (ecpUMap G x₀) .X).node
            ((ecpNMap (ecpUMap G x₀) .X).node (.icp (.icp x))) = .X then .X
          else .icp ((ecpNMap (ecpUMap G x₀) .X).node (.icp (.icp x))) := rfl
  rw [hrw, ite_eq_right hne, ite_eq_right hne2, e1]

/-! #### The node cycle around the new darts -/

/-- The dart before the new dart in the node cycle of a `U` step. -/
theorem node_inv_ecpU_X : (ecpUMap G x₀).node⁻¹ (.X : EcpDart D) = .icp (G.node x₀) := by
  refine Equiv.Perm.inv_eq_iff_eq.mpr ?_
  have hn : (ecpUMap G x₀).node (.icp (G.node x₀)) = .X := ite_eq_left rfl
  rw [hn]

/-- Two darts before the new dart in the node cycle of a `U` step. -/
theorem node_inv_ecpU_icp_node (h : G.ProperCpring x₀) :
    (ecpUMap G x₀).node⁻¹ (.icp (G.node x₀) : EcpDart D) = .icp x₀ := by
  refine Equiv.Perm.inv_eq_iff_eq.mpr ?_
  rw [ecpUMap_node, ecpUNode_icp_of_ne G x₀ h]

/-- The node map of a `Y` step on an old dart that is not the new one. -/
theorem node_ecpY_of (v : EcpDart D) (h1 : v ≠ .X)
    (h2 : (ecpUMap G x₀).node ((ecpUMap G x₀).node v) ≠ .X) :
    (ecpNMap (ecpUMap G x₀) .X).node (.icp v) = .icp ((ecpUMap G x₀).node v) := by
  rw [ecpNMap_node, ecpNNode_icp, ite_eq_right h1, ite_eq_right h2]

/-- The node map of a `Y` step on the dart two node steps before the new one. -/
theorem node_ecpY_of_eq (v : EcpDart D) (h1 : v ≠ .X)
    (h2 : (ecpUMap G x₀).node ((ecpUMap G x₀).node v) = .X) :
    (ecpNMap (ecpUMap G x₀) .X).node (.icp v) = .X := by
  rw [ecpNMap_node, ecpNNode_icp, ite_eq_right h1, ite_eq_left h2]

/-- The dart before the new dart in the node cycle of a `Y` step. -/
theorem node_inv_ecpY_X (h : G.ProperCpring x₀) :
    (ecpNMap (ecpUMap G x₀) .X).node⁻¹ (.X : EcpDart (EcpDart D)) = .icp (.icp x₀) := by
  refine Equiv.Perm.inv_eq_iff_eq.mpr ?_
  have hU1 : (ecpUMap G x₀).node (.icp x₀) = .icp (G.node x₀) := by
    rw [ecpUMap_node, ecpUNode_icp_of_ne G x₀ h]
  have hU2 : (ecpUMap G x₀).node (.icp (G.node x₀)) = .X := ite_eq_left rfl
  have h2 : (ecpUMap G x₀).node ((ecpUMap G x₀).node (.icp x₀)) = .X := by rw [hU1, hU2]
  rw [node_ecpY_of_eq G x₀ (.icp x₀) (by simp) h2]

/-- Two darts before the new dart in the node cycle of a `Y` step, long case. -/
theorem node_inv_ecpY_icpY_of_long (h : G.LongCpring x₀) :
    (ecpNMap (ecpUMap G x₀) .X).node⁻¹ (.icp (.icp x₀)) = .icp (.icp (G.node⁻¹ x₀)) := by
  refine Equiv.Perm.inv_eq_iff_eq.mpr ?_
  have hp : G.ProperCpring x₀ := h.properCpring
  have hne : G.node⁻¹ x₀ ≠ G.node x₀ := longCpring_iff_inv_ne.mp h
  have hU1 : (ecpUMap G x₀).node (.icp (G.node⁻¹ x₀)) = .icp x₀ := by
    rw [ecpUMap_node, ecpUNode_icp_of_ne G x₀ hne, node_inv_node]
  have hU2 : (ecpUMap G x₀).node (.icp x₀) = .icp (G.node x₀) := by
    rw [ecpUMap_node, ecpUNode_icp_of_ne G x₀ hp]
  have h2 : (ecpUMap G x₀).node ((ecpUMap G x₀).node (.icp (G.node⁻¹ x₀))) ≠ .X := by
    rw [hU1, hU2]; simp
  rw [node_ecpY_of G x₀ (.icp (G.node⁻¹ x₀)) (by simp) h2, hU1]

/-- Two darts before the new dart in the node cycle of a `Y` step, short case. -/
theorem node_inv_ecpY_icpY_of_not_long (hp : G.ProperCpring x₀) (h : ¬ G.LongCpring x₀) :
    (ecpNMap (ecpUMap G x₀) .X).node⁻¹ (.icp (.icp x₀)) = .icp .Xe := by
  refine Equiv.Perm.inv_eq_iff_eq.mpr ?_
  have hinv : G.node⁻¹ x₀ = G.node x₀ := by
    by_contra hc
    exact h (longCpring_iff_inv_ne.mpr hc)
  have hnn : G.node (G.node x₀) = x₀ := by
    have hc := congrArg G.node hinv
    rw [node_inv_node] at hc
    exact hc.symm
  have hU1 : (ecpUMap G x₀).node (.Xe : EcpDart D) = .icp (G.node (G.node x₀)) := rfl
  have hU2 : (ecpUMap G x₀).node (.icp x₀) = .icp (G.node x₀) := by
    rw [ecpUMap_node, ecpUNode_icp_of_ne G x₀ hp]
  have h2 : (ecpUMap G x₀).node ((ecpUMap G x₀).node (.Xe : EcpDart D)) ≠ .X := by
    rw [hU1, hnn, hU2]; simp
  rw [node_ecpY_of G x₀ .Xe (by simp) h2, hU1, hnn]

/-! #### The faces around the new dart of a `Y` step -/

/-- The node of the new dart of a `Y` step lies on the face of `node x₀`. -/
theorem cface_icpXe_ecpY :
    (ecpNMap (ecpUMap G x₀) .X).CFace (.icp .Xe) (.icp (.icp (G.node x₀))) :=
  (cface_icpN (ecpUMap G x₀) .X .Xe (.icp (G.node x₀))).mpr
    ((cface_Xe_icpU G x₀ (G.node x₀)).mpr (Equiv.Perm.SameCycle.refl _ _))

/-- The second new dart of a `Y` step lies on the face of `x₀`. -/
theorem cface_Xe_ecpY (h : G.ProperCpring x₀) :
    (ecpNMap (ecpUMap G x₀) .X).CFace .Xe (.icp (.icp x₀)) := by
  refine (cface_Xe_icpN (ecpUMap G x₀) .X (.icp x₀)).mpr ?_
  rw [node_inv_ecpU_X, node_inv_ecpU_icp_node G x₀ h]

/-- The face of the new dart of a `Y` step has exactly two darts. -/
theorem cface_ecpY_iff (u : EcpDart (EcpDart D)) :
    (ecpNMap (ecpUMap G x₀) .X).CFace .X u ↔ u = .X ∨ u = .icp .X := by
  have hlong := longCpring_ecpU G x₀
  have hb : (ecpUMap G x₀).node⁻¹ ((ecpUMap G x₀).node⁻¹ (.X : EcpDart D)) ≠ .X := fun hc =>
    longCpring_iff_inv_ne.mp hlong ((inv_inv_node_eq_iff (ecpUMap G x₀) .X).mp hc)
  cases u with
  | X => exact ⟨fun _ => Or.inl rfl, fun _ => Equiv.Perm.SameCycle.refl _ _⟩
  | Xe =>
    rw [cface_ecpN_Xe (ecpUMap G x₀) .X]
    refine ⟨fun hc => absurd ((cface_ecpU G x₀ _).mp hc) hb, ?_⟩
    rintro (hc | hc) <;> exact absurd hc (by simp)
  | icp v =>
    rw [cface_ecpN_icp (ecpUMap G x₀) .X v]
    constructor
    · intro hc
      exact Or.inr (congrArg EcpDart.icp ((cface_ecpU G x₀ v).mp hc.symm))
    · rintro (hc | hc)
      · exact absurd hc (by simp)
      · rw [EcpDart.icp_injective hc]

/-- The dart two node steps before the new dart of a `Y` step lies on the face
of `node⁻¹ x₀`. -/
theorem cface_b2_ecpY (h : G.ProperCpring x₀) :
    (ecpNMap (ecpUMap G x₀) .X).CFace
      ((ecpNMap (ecpUMap G x₀) .X).node⁻¹ ((ecpNMap (ecpUMap G x₀) .X).node⁻¹ .X))
      (.icp (.icp (G.node⁻¹ x₀))) := by
  rw [node_inv_ecpY_X G x₀ h]
  by_cases hl : G.LongCpring x₀
  · rw [node_inv_ecpY_icpY_of_long G x₀ hl]
  · rw [node_inv_ecpY_icpY_of_not_long G x₀ h hl]
    have hinv : G.node⁻¹ x₀ = G.node x₀ := by
      by_contra hc
      exact hl (longCpring_iff_inv_ne.mpr hc)
    rw [hinv]
    exact cface_icpXe_ecpY G x₀

/-- **The faces adjacent to the new face of a `Y` step**: the faces of
`node x₀` and of `x₀`. -/
theorem adj_ecpY (h : G.ProperCpring x₀) (u : EcpDart (EcpDart D)) :
    (ecpNMap (ecpUMap G x₀) .X).Adj .X u ↔
      (ecpNMap (ecpUMap G x₀) .X).CFace u (.icp (.icp (G.node x₀)))
        ∨ (ecpNMap (ecpUMap G x₀) .X).CFace u (.icp (.icp x₀)) := by
  have hXe : (ecpNMap (ecpUMap G x₀) .X).CFace .Xe (.icp (.icp x₀)) := cface_Xe_ecpY G x₀ h
  have hnY : (ecpNMap (ecpUMap G x₀) .X).CFace (.icp .Xe) (.icp (.icp (G.node x₀))) :=
    cface_icpXe_ecpY G x₀
  have he1 : (ecpNMap (ecpUMap G x₀) .X).edge (.X : EcpDart (EcpDart D)) = .Xe := rfl
  have he2 : (ecpNMap (ecpUMap G x₀) .X).edge (.icp (.X : EcpDart D)) = .icp .Xe := rfl
  constructor
  · rintro ⟨z, hz, hrz⟩
    rcases (cface_ecpY_iff G x₀ z).mp hz with rfl | rfl
    · rw [Rlink, he1] at hrz
      exact Or.inr (hrz.symm.trans hXe)
    · rw [Rlink, he2] at hrz
      exact Or.inl (hrz.symm.trans hnY)
  · rintro (h1 | h1)
    · refine ⟨.icp .X, (cface_ecpY_iff G x₀ _).mpr (Or.inr rfl), ?_⟩
      rw [Rlink, he2]
      exact hnY.trans h1.symm
    · refine ⟨.X, (cface_ecpY_iff G x₀ _).mpr (Or.inl rfl), ?_⟩
      rw [Rlink, he1]
      exact hXe.trans h1.symm

/-- **The faces adjacent to the new face of an `H` step**: the faces of
`node x₀`, of `x₀` and of `node⁻¹ x₀`. -/
theorem adj_ecpH (h : G.ProperCpring x₀) (u : EcpDart (EcpDart (EcpDart D))) :
    (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).Adj .X u ↔
      (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).CFace u (.icp (.icp (.icp (G.node x₀))))
        ∨ (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).CFace u (.icp (.icp (.icp x₀)))
        ∨ (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).CFace u
            (.icp (.icp (.icp (G.node⁻¹ x₀)))) := by
  have hlY : (ecpNMap (ecpUMap G x₀) .X).LongCpring .X := by
    refine longCpring_ecpN_of_long (ecpUMap G x₀) .X (longCpring_ecpU G x₀) ?_
    rw [length_cpring_ecpU]
    have hp := proper_cpring_iff.mp h
    omega
  have hb2 : ¬ (ecpNMap (ecpUMap G x₀) .X).CFace .X
      ((ecpNMap (ecpUMap G x₀) .X).node⁻¹ ((ecpNMap (ecpUMap G x₀) .X).node⁻¹ .X)) := by
    rw [cface_ecpY_iff]
    rintro (hc | hc)
    · exact longCpring_iff_inv_ne.mp hlY
        ((inv_inv_node_eq_iff (ecpNMap (ecpUMap G x₀) .X) .X).mp hc)
    · rw [node_inv_ecpY_X G x₀ h] at hc
      by_cases hl : G.LongCpring x₀
      · rw [node_inv_ecpY_icpY_of_long G x₀ hl] at hc
        exact absurd hc (by simp)
      · rw [node_inv_ecpY_icpY_of_not_long G x₀ h hl] at hc
        exact absurd hc (by simp)
  have hb2eq : ∀ w : EcpDart (EcpDart D),
      (ecpNMap (ecpUMap G x₀) .X).CFace w
          ((ecpNMap (ecpUMap G x₀) .X).node⁻¹ ((ecpNMap (ecpUMap G x₀) .X).node⁻¹ .X))
        ↔ (ecpNMap (ecpUMap G x₀) .X).CFace w (.icp (.icp (G.node⁻¹ x₀))) :=
    fun w => ⟨fun hc => hc.trans (cface_b2_ecpY G x₀ h),
      fun hc => hc.trans (cface_b2_ecpY G x₀ h).symm⟩
  have hfaceX : (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).CFace .X (.icp .X) :=
    cface_ecpN (ecpNMap (ecpUMap G x₀) .X) .X
  obtain ⟨v, hv⟩ := fband_icpN (ecpNMap (ecpUMap G x₀) .X) .X u
  have hconv : ∀ w : EcpDart (EcpDart D),
      (ecpNMap (ecpNMap (ecpUMap G x₀) .X) .X).CFace u (.icp w)
        ↔ (ecpNMap (ecpUMap G x₀) .X).CFace v w := by
    intro w
    rw [← cface_icpN (ecpNMap (ecpUMap G x₀) .X) .X v w]
    exact ⟨fun hc => hv.symm.trans hc, fun hc => hv.trans hc⟩
  rw [adj_congr_left hfaceX, adj_congr_right hv, adj_icpN, hconv, hconv, hconv,
    adj_ecpY G x₀ h v]
  constructor
  · rintro ((h1 | h1) | ⟨h1, -⟩ | ⟨-, h1⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact absurd h1 hb2
    · exact Or.inr (Or.inr ((hb2eq v).mp h1))
  · rintro (h1 | h1 | h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (Or.inr ⟨Equiv.Perm.SameCycle.refl _ _, (hb2eq v).mpr h1⟩)

end EcpComposite

end Hypermap

/-! ### The A step: merging the neighbours of a face -/

namespace Hypermap

section EcpA

variable [Finite D] [DecidableEq D] (G : Hypermap D) (x₀ : D)

open Classical in
/-- The edge map of an `A` step.  When the two neighbours of the face of `x₀`
are already merged a new hyperedge is created, so that the step never
disconnects the map. -/
noncomputable def ecpAEdge : D → D := fun x =>
  if G.CFace (G.edge x₀) (G.node x₀) then
    (if x = x₀ then G.edge (G.node (G.node x₀))
     else if x = G.node (G.node x₀) then G.edge x₀ else G.edge x)
  else G.edge x

/-- The node map of an `A` step. -/
noncomputable def ecpANode : D → D := fun x =>
  if x = G.node x₀ then x₀
  else if G.node x = x₀ then G.node (G.node x₀) else G.node x

open Classical in
/-- The face map of an `A` step. -/
noncomputable def ecpAFace : D → D := fun x =>
  if G.CFace (G.edge x₀) (G.node x₀) then G.face x
  else if x = G.edge x₀ then G.node x₀
  else if G.face x = G.node x₀ then G.face (G.edge x₀) else G.face x

omit [Finite D] in
/-- The `A` node map at the head of the ring. -/
theorem ecpANode_node : ecpANode G x₀ (G.node x₀) = x₀ := ite_eq_left rfl

omit [Finite D] in
/-- The `A` node map at the last dart of the ring. -/
theorem ecpANode_inv (h : G.node (G.node x₀) ≠ x₀) :
    ecpANode G x₀ (G.node⁻¹ x₀) = G.node (G.node x₀) := by
  have h1 : G.node⁻¹ x₀ ≠ G.node x₀ := by
    intro hcc
    refine h ?_
    have hd := congrArg (fun z => G.node z) hcc
    simp only [node_inv_node] at hd
    exact hd.symm
  change (if G.node⁻¹ x₀ = G.node x₀ then x₀ else
    if G.node (G.node⁻¹ x₀) = x₀ then G.node (G.node x₀) else G.node (G.node⁻¹ x₀)) = _
  rw [ite_eq_right h1, ite_eq_left (node_inv_node G x₀)]

omit [Finite D] in
/-- The `A` node map away from the two modified darts. -/
theorem ecpANode_inv_gen {x : D} (h1 : x ≠ G.node (G.node x₀)) (h2 : x ≠ x₀) :
    ecpANode G x₀ (G.node⁻¹ x) = x := by
  have ha : G.node⁻¹ x ≠ G.node x₀ := by
    intro hcc
    refine h1 ?_
    have hd := congrArg (fun z => G.node z) hcc
    simpa only [node_inv_node] using hd
  have hb : G.node (G.node⁻¹ x) ≠ x₀ := by rw [node_inv_node]; exact h2
  change (if G.node⁻¹ x = G.node x₀ then x₀ else
    if G.node (G.node⁻¹ x) = x₀ then G.node (G.node x₀) else G.node (G.node⁻¹ x)) = _
  rw [ite_eq_right ha, ite_eq_right hb, node_inv_node]

omit [Finite D] in
/-- The three maps of an `A` step satisfy the hypermap identity. -/
theorem ecpA_cancel3 (x : D) : ecpANode G x₀ (ecpAFace G x₀ (ecpAEdge G x₀ x)) = x := by
  classical
  by_cases hc : G.CFace (G.edge x₀) (G.node x₀)
  · have hface : ∀ y : D, ecpAFace G x₀ y = G.face y := fun y => ite_eq_left hc
    rw [hface]
    by_cases h0 : x = x₀
    · have he : ecpAEdge G x₀ x = G.edge (G.node (G.node x₀)) := by
        change (if G.CFace (G.edge x₀) (G.node x₀) then
          (if x = x₀ then G.edge (G.node (G.node x₀))
           else if x = G.node (G.node x₀) then G.edge x₀ else G.edge x) else G.edge x) = _
        rw [ite_eq_left hc, ite_eq_left h0]
      rw [he, G.face_edge, inv_node_node, ecpANode_node, h0]
    · by_cases h1 : x = G.node (G.node x₀)
      · have he : ecpAEdge G x₀ x = G.edge x₀ := by
          change (if G.CFace (G.edge x₀) (G.node x₀) then
            (if x = x₀ then G.edge (G.node (G.node x₀))
             else if x = G.node (G.node x₀) then G.edge x₀ else G.edge x) else G.edge x) = _
          rw [ite_eq_left hc, ite_eq_right h0, ite_eq_left h1]
        rw [he, G.face_edge, ecpANode_inv G x₀ (fun hcc => h0 (h1.trans hcc)), h1]
      · have he : ecpAEdge G x₀ x = G.edge x := by
          change (if G.CFace (G.edge x₀) (G.node x₀) then
            (if x = x₀ then G.edge (G.node (G.node x₀))
             else if x = G.node (G.node x₀) then G.edge x₀ else G.edge x) else G.edge x) = _
          rw [ite_eq_left hc, ite_eq_right h0, ite_eq_right h1]
        rw [he, G.face_edge, ecpANode_inv_gen G x₀ h1 h0]
  · have he : ecpAEdge G x₀ x = G.edge x := by
      change (if G.CFace (G.edge x₀) (G.node x₀) then
        (if x = x₀ then G.edge (G.node (G.node x₀))
         else if x = G.node (G.node x₀) then G.edge x₀ else G.edge x) else G.edge x) = _
      rw [ite_eq_right hc]
    rw [he]
    have hfaceq : ∀ y : D, ecpAFace G x₀ y =
        if y = G.edge x₀ then G.node x₀
        else if G.face y = G.node x₀ then G.face (G.edge x₀) else G.face y := by
      intro y
      change (if G.CFace (G.edge x₀) (G.node x₀) then G.face y else
        if y = G.edge x₀ then G.node x₀
        else if G.face y = G.node x₀ then G.face (G.edge x₀) else G.face y) = _
      rw [ite_eq_right hc]
    rw [hfaceq]
    by_cases h0 : x = x₀
    · rw [ite_eq_left (by rw [h0]), ecpANode_node, h0]
    · have h0' : G.edge x ≠ G.edge x₀ := fun hcc => h0 (G.edge.injective hcc)
      rw [ite_eq_right h0', G.face_edge]
      by_cases h1 : G.node⁻¹ x = G.node x₀
      · have hx : x = G.node (G.node x₀) := by
          have hd := congrArg (fun z => G.node z) h1
          simpa only [node_inv_node] using hd
        rw [ite_eq_left h1, G.face_edge, ecpANode_inv G x₀ (fun hcc => h0 (hx.trans hcc)), hx]
      · have hx : x ≠ G.node (G.node x₀) := by
          intro hcc
          refine h1 ?_
          rw [hcc, inv_node_node]
        rw [ite_eq_right h1, ecpANode_inv_gen G x₀ hx h0]

/-- The hypermap obtained by an `A` step at `x₀`. -/
noncomputable def ecpAMap : Hypermap D :=
  ofCancel3 (ecpAEdge G x₀) (ecpANode G x₀) (ecpAFace G x₀) (ecpA_cancel3 G x₀)

/-- The reference dart after an `A` step. -/
noncomputable def ecpAPoint : D := ecpAFace G x₀ (ecpAEdge G x₀ (G.face (G.edge x₀)))

/-! #### The face and node maps of an `A` step as transpositions -/

omit [Finite D] in
/-- The node map of an `A` step away from the two modified darts. -/
theorem ecpANode_of_ne {x : D} (h1 : x ≠ G.node x₀) (h2 : G.node x ≠ x₀) :
    ecpANode G x₀ x = G.node x := by
  change (if x = G.node x₀ then x₀
    else if G.node x = x₀ then G.node (G.node x₀) else G.node x) = _
  rw [ite_eq_right h1, ite_eq_right h2]

/-- The node map of an `A` step is the node map of `G` followed by the
transposition of `x₀` and `node (node x₀)`. -/
theorem ecpAMap_node_eq :
    (ecpAMap G x₀).node = Equiv.swap x₀ (G.node (G.node x₀)) * G.node := by
  ext x
  rw [Perm.mul_apply]
  have hlhs : (ecpAMap G x₀).node x
      = if x = G.node x₀ then x₀
        else if G.node x = x₀ then G.node (G.node x₀) else G.node x := rfl
  rw [hlhs]
  by_cases h1 : x = G.node x₀
  · rw [ite_eq_left h1, h1, Equiv.swap_apply_right]
  · rw [ite_eq_right h1]
    by_cases h2 : G.node x = x₀
    · rw [ite_eq_left h2, h2, Equiv.swap_apply_left]
    · have h3 : G.node x ≠ G.node (G.node x₀) := fun hc => h1 (G.node.injective hc)
      rw [ite_eq_right h2, Equiv.swap_apply_of_ne_of_ne h2 h3]

/-- When the two neighbours of the face of `x₀` are already merged, an `A` step
leaves the face map alone. -/
theorem ecpAMap_face_of_merged (h : G.CFace (G.edge x₀) (G.node x₀)) :
    (ecpAMap G x₀).face = G.face := by
  classical
  ext x
  have hlhs : (ecpAMap G x₀).face x
      = if G.CFace (G.edge x₀) (G.node x₀) then G.face x
        else if x = G.edge x₀ then G.node x₀
        else if G.face x = G.node x₀ then G.face (G.edge x₀) else G.face x := rfl
  rw [hlhs, ite_eq_left h]

/-- Otherwise an `A` step merges the two faces by transposing `node x₀` and
`node⁻¹ x₀`. -/
theorem ecpAMap_face_of_not_merged (h : ¬ G.CFace (G.edge x₀) (G.node x₀)) :
    (ecpAMap G x₀).face = Equiv.swap (G.node x₀) (G.node⁻¹ x₀) * G.face := by
  classical
  ext x
  rw [Perm.mul_apply]
  have hlhs : (ecpAMap G x₀).face x
      = if G.CFace (G.edge x₀) (G.node x₀) then G.face x
        else if x = G.edge x₀ then G.node x₀
        else if G.face x = G.node x₀ then G.face (G.edge x₀) else G.face x := rfl
  rw [hlhs, ite_eq_right h, G.face_edge]
  by_cases h1 : x = G.edge x₀
  · have hfx : G.face x = G.node⁻¹ x₀ := by rw [h1, G.face_edge]
    rw [ite_eq_left h1, hfx, Equiv.swap_apply_right]
  · have hfx : G.face x ≠ G.node⁻¹ x₀ := by
      intro hc
      refine h1 (G.face.injective ?_)
      rw [hc, G.face_edge]
    rw [ite_eq_right h1]
    by_cases h2 : G.face x = G.node x₀
    · rw [ite_eq_left h2, h2, Equiv.swap_apply_left]
    · rw [ite_eq_right h2, Equiv.swap_apply_of_ne_of_ne h2 hfx]

omit [Finite D] [DecidableEq D] in
/-- The dart `node⁻¹ x₀` lies on the face of `edge x₀`. -/
theorem cface_inv_node_edge : G.CFace (G.edge x₀) (G.node⁻¹ x₀) := by
  have h := G.cface_face (G.edge x₀)
  rwa [G.face_edge] at h

/-- **The faces of an `A` step**: the step merges the face of `node x₀` with the
face of `node⁻¹ x₀` and leaves all other faces alone. -/
theorem cface_icpA (x y : D) :
    (ecpAMap G x₀).CFace x y ↔ G.CFace x y ∨
      ((G.CFace x (G.node x₀) ∨ G.CFace x (G.node⁻¹ x₀)) ∧
        (G.CFace y (G.node x₀) ∨ G.CFace y (G.node⁻¹ x₀))) := by
  by_cases h : G.CFace (G.edge x₀) (G.node x₀)
  · have hab : G.CFace (G.node⁻¹ x₀) (G.node x₀) :=
      (cface_inv_node_edge G x₀).symm.trans h
    have hiff : (ecpAMap G x₀).CFace x y ↔ G.face.SameCycle x y := by
      change (ecpAMap G x₀).face.SameCycle x y ↔ G.face.SameCycle x y
      rw [ecpAMap_face_of_merged G x₀ h]
    rw [hiff]
    refine ⟨fun hc => Or.inl hc, ?_⟩
    rintro (hc | ⟨hx, hy⟩)
    · exact hc
    · rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hx.trans hy.symm
      · exact hx.trans (hab.symm.trans hy.symm)
      · exact hx.trans (hab.trans hy.symm)
      · exact hx.trans hy.symm
  · have hb : G.CFace (G.edge x₀) (G.node⁻¹ x₀) := cface_inv_node_edge G x₀
    have hne : G.node x₀ ≠ G.node⁻¹ x₀ := fun hc => h (by rw [hc]; exact hb)
    have hns : ¬ G.face.SameCycle (G.node x₀) (G.node⁻¹ x₀) := fun hc =>
      h (hb.trans hc.symm)
    have hiff : (ecpAMap G x₀).CFace x y
        ↔ (Equiv.swap (G.node x₀) (G.node⁻¹ x₀) * G.face).SameCycle x y := by
      change (ecpAMap G x₀).face.SameCycle x y ↔ _
      rw [ecpAMap_face_of_not_merged G x₀ h]
    rw [hiff, sameCycle_swap_mul hne hns]
    constructor
    · rintro (hc | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨Or.inl h1, Or.inr h2⟩
      · exact Or.inr ⟨Or.inr h1, Or.inl h2⟩
    · rintro (hc | ⟨hx, hy⟩)
      · exact Or.inl hc
      · rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (hx.trans hy.symm)
        · exact Or.inr (Or.inl ⟨hx, hy⟩)
        · exact Or.inr (Or.inr ⟨hx, hy⟩)
        · exact Or.inl (hx.trans hy.symm)

/-- An `A` step preserves face orbits. -/
theorem sub_cface_icpA {x y : D} (h : G.CFace x y) : (ecpAMap G x₀).CFace x y :=
  (cface_icpA G x₀ x y).mpr (Or.inl h)

/-- **The merge of an `A` step**: the two neighbours of the face of `x₀` end up
on a common face. -/
theorem ecpA_merge : (ecpAMap G x₀).CFace (G.node⁻¹ x₀) (G.node x₀) :=
  (cface_icpA G x₀ _ _).mpr
    (Or.inr ⟨Or.inr (SameCycle.refl _ _), Or.inl (SameCycle.refl _ _)⟩)

/-- An `A` step preserves adjacency. -/
theorem sub_adj_icpA {x y : D} (hxy : G.Adj x y) : (ecpAMap G x₀).Adj x y := by
  classical
  obtain ⟨z, hz, hrz⟩ := hxy
  have hedgeA : ecpAEdge G x₀ z
      = if G.CFace (G.edge x₀) (G.node x₀) then
          (if z = x₀ then G.edge (G.node (G.node x₀))
           else if z = G.node (G.node x₀) then G.edge x₀ else G.edge z)
        else G.edge z := rfl
  refine ⟨z, sub_cface_icpA G x₀ hz, ?_⟩
  by_cases h : G.CFace (G.edge x₀) (G.node x₀)
  · have hface : (ecpAMap G x₀).face = G.face := ecpAMap_face_of_merged G x₀ h
    have hiff : ∀ a b : D, (ecpAMap G x₀).CFace a b ↔ G.CFace a b := by
      intro a b
      change (ecpAMap G x₀).face.SameCycle a b ↔ G.face.SameCycle a b
      rw [hface]
    have hkey : G.CFace (G.edge (G.node (G.node x₀))) (G.node x₀) := by
      have hc := G.cface_face (G.edge (G.node (G.node x₀)))
      rwa [G.nodeK] at hc
    have hgoal : G.CFace (ecpAEdge G x₀ z) y := by
      rw [hedgeA, ite_eq_left h]
      by_cases h0 : z = x₀
      · rw [ite_eq_left h0]
        rw [h0] at hrz
        exact hkey.trans (h.symm.trans hrz)
      · rw [ite_eq_right h0]
        by_cases h1 : z = G.node (G.node x₀)
        · rw [ite_eq_left h1]
          rw [h1] at hrz
          exact h.trans (hkey.symm.trans hrz)
        · rw [ite_eq_right h1]
          exact hrz
    exact (hiff _ y).mpr hgoal
  · have hedge : ecpAEdge G x₀ z = G.edge z := by rw [hedgeA, ite_eq_right h]
    have hsub := sub_cface_icpA G x₀ hrz
    rw [← hedge] at hsub
    exact hsub

/-! #### The ring of an `A` step -/

/-- The reference dart of an `A` step has `node⁻¹ x₀` as its node image. -/
theorem node_ecpAPoint : (ecpAMap G x₀).node (ecpAPoint G x₀) = G.node⁻¹ x₀ := by
  have h : (ecpAMap G x₀).node (ecpAPoint G x₀) = G.face (G.edge x₀) :=
    ecpA_cancel3 G x₀ (G.face (G.edge x₀))
  rw [h, G.face_edge]

omit [Finite D] [DecidableEq D] in
/-- A long ring has more than two darts around its node. -/
theorem node_node_ne_of_long (h : G.LongCpring x₀) : G.node (G.node x₀) ≠ x₀ := by
  intro hc
  refine h ?_
  rw [G.face_edge]
  have hinv : G.node⁻¹ x₀ = G.node⁻¹ (G.node (G.node x₀)) := by rw [hc]
  rw [hinv, inv_node_node]

/-- The ring after an `A` step at a long ring loses its first two darts. -/
theorem cpring_ecpA_of_long (h : G.LongCpring x₀) :
    (ecpAMap G x₀).cpring (ecpAPoint G x₀) = (G.cpring x₀).drop 2 := by
  obtain ⟨d, hd⟩ : ∃ d, (G.cpring x₀).drop 3 = d := ⟨_, rfl⟩
  have hc3 : G.cpring x₀ = G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d := by
    rw [← hd, ← G.face_edge x₀]
    exact head_long_cpring h
  have hdrop : (G.cpring x₀).drop 2 = G.node⁻¹ x₀ :: d := by rw [hc3]; rfl
  have hnd : (G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d).Nodup := hc3 ▸ nodup_cpring
  have hchain : List.IsChain (fun u v => u = G.node v)
      (G.node x₀ :: x₀ :: G.node⁻¹ x₀ :: d) := hc3 ▸ isCyclicChain_cpring.isChain
  have hnn : G.node (G.node x₀) ≠ x₀ := node_node_ne_of_long G x₀ h
  have hnx₀d : G.node x₀ ∉ d := fun hc =>
    (List.nodup_cons.mp hnd).1 (by simp [hc])
  have hinvd : G.node⁻¹ x₀ ∉ d :=
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
  have hnode : (ecpAMap G x₀).node (ecpAPoint G x₀) = G.node⁻¹ x₀ := node_ecpAPoint G x₀
  rw [hdrop]
  refine cpring_eq ?_ ?_ (by simp) (by rw [hnode]; rfl)
  · constructor
    · refine (hchain.tail.tail).imp_of_mem_tail_imp ?_
      intro a b _ hb hab
      have hb1 : b ≠ G.node x₀ := fun hc => hnx₀d (hc ▸ hb)
      have hb2 : G.node b ≠ x₀ := by
        intro hc
        refine hinvd ?_
        have hbb : b = G.node⁻¹ x₀ := by rw [← hc, inv_node_node]
        exact hbb ▸ hb
      change (a : D) = ecpANode G x₀ b
      rw [ecpANode_of_ne G x₀ hb1 hb2, hab]
    · intro a ha b hb
      obtain rfl : b = G.node⁻¹ x₀ := (Option.some.injEq _ _).mp hb.symm
      have hlast : a = G.node (G.node x₀) := by
        have hlastring : (G.cpring x₀).getLast? = some a := by
          rw [hc3, getLast?_cons_ne_nil (by simp), getLast?_cons_ne_nil (by simp)]
          exact ha
        have hhead : (G.cpring x₀).head? = some (G.node x₀) := by rw [hc3]; rfl
        exact isCyclicChain_cpring.2 a hlastring (G.node x₀) hhead
      change (a : D) = ecpANode G x₀ (G.node⁻¹ x₀)
      rw [ecpANode_inv G x₀ hnn, hlast]
  · exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2

/-- The ring after an `A` step at a short ring is unchanged. -/
theorem cpring_ecpA_of_not_long (h : ¬ G.LongCpring x₀) :
    (ecpAMap G x₀).cpring (ecpAPoint G x₀) = G.cpring x₀ := by
  have hl : G.node⁻¹ x₀ = G.node x₀ := by rw [← G.face_edge x₀]; exact not_not.mp h
  have hnode : (ecpAMap G x₀).node (ecpAPoint G x₀) = G.node x₀ := by
    rw [node_ecpAPoint, hl]
  have hlen : ¬ 2 < (G.cpring x₀).length := fun hc => h (long_cpring_iff.mpr hc)
  have hpos : 0 < (G.cpring x₀).length := length_cpring_pos
  by_cases hp : G.ProperCpring x₀
  · have h2 : (G.cpring x₀).length = 2 := by
      have := proper_cpring_iff.mp hp
      omega
    have hc2 : G.cpring x₀ = G.node x₀ :: x₀ :: (G.cpring x₀).drop 2 :=
      head_proper_cpring hp
    have hdnil : (G.cpring x₀).drop 2 = [] := by
      rw [← List.length_eq_zero_iff, List.length_drop, h2]
    rw [hdnil] at hc2
    have hnn : G.node (G.node x₀) = x₀ := by
      have hd := congrArg G.node hl
      rw [node_inv_node] at hd
      exact hd.symm
    refine cpring_eq ?_ ?_ (by rw [hc2]; simp) (by rw [hnode, hc2]; rfl)
    · rw [hc2]
      constructor
      · rw [List.isChain_cons_cons]
        refine ⟨?_, List.isChain_singleton _⟩
        change G.node x₀ = ecpANode G x₀ x₀
        have hx1 : x₀ ≠ G.node x₀ := hp
        have hx2 : G.node x₀ ≠ x₀ := fun hc => hp hc.symm
        rw [ecpANode_of_ne G x₀ hx1 hx2]
      · intro a ha b hb
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
          Option.some.injEq] at ha
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst ha; subst hb
        change x₀ = ecpANode G x₀ (G.node x₀)
        rw [ecpANode_node]
    · exact nodup_cpring
  · have h1 : (G.cpring x₀).length = 1 := by
      have hnp : ¬ 1 < (G.cpring x₀).length := fun hc => hp (proper_cpring_iff.mpr hc)
      omega
    have hx : x₀ = G.node x₀ := not_not.mp hp
    have hc1 : G.cpring x₀ = [G.node x₀] := by
      have hc := head_cpring (G := G) (x₀ := x₀)
      have htl : (G.cpring x₀).tail = [] := by
        rw [← List.length_eq_zero_iff, List.length_tail, h1]
      rw [htl] at hc
      exact hc
    refine cpring_eq ?_ ?_ (by rw [hc1]; simp) (by rw [hnode, hc1]; rfl)
    · rw [hc1, isCyclicChain_singleton]
      change G.node x₀ = ecpANode G x₀ (G.node x₀)
      rw [ecpANode_node]
      exact hx.symm
    · exact nodup_cpring

/-- The ring after an `A` step loses two darts, unless it had at most two. -/
theorem length_cpring_ecpA :
    ((ecpAMap G x₀).cpring (ecpAPoint G x₀)).length
      = if 2 < (G.cpring x₀).length then (G.cpring x₀).length - 2
        else (G.cpring x₀).length := by
  by_cases h : G.LongCpring x₀
  · have hlen := long_cpring_iff.mp h
    rw [cpring_ecpA_of_long G x₀ h, List.length_drop, ite_eq_left hlen]
  · have hlen : ¬ 2 < (G.cpring x₀).length := fun hc => h (long_cpring_iff.mpr hc)
    rw [cpring_ecpA_of_not_long G x₀ h, ite_eq_right hlen]

end EcpA

end Hypermap

/-! ### The step constructions on pointed maps -/

namespace PointedMap

/-- The hypermap of a single edge: two darts, swapped by `edge` and by `node`,
and fixed by `face`. -/
noncomputable def cpmap0Map : Hypermap Bool :=
  Hypermap.ofCancel3 (fun b => !b) (fun b => !b) id (by decide)

/-- The map of a single edge.  This is the starting point of every
construction. -/
noncomputable def cpmap0 : PointedMap := ⟨Bool, inferInstance, inferInstance, cpmap0Map, true⟩

/-- The `R n` step: rotate the reference dart `n` steps around the ring. -/
noncomputable def ecpR (n : ℕ) (M : PointedMap) : PointedMap :=
  ⟨M.Dart, M.finite, M.decEq, M.map, M.map.ecpRPoint M.point n⟩

/-- The `U` step: add a new disconnected face. -/
noncomputable def ecpU (M : PointedMap) : PointedMap :=
  ⟨EcpDart M.Dart, inferInstance, inferInstance, M.map.ecpUMap M.point, .X⟩

/-- The `N` step: close off a face. -/
noncomputable def ecpN (M : PointedMap) : PointedMap :=
  ⟨EcpDart M.Dart, inferInstance, inferInstance, M.map.ecpNMap M.point, .X⟩

/-- The `A` step: merge the two neighbours of the face of the reference dart. -/
noncomputable def ecpA (M : PointedMap) : PointedMap :=
  ⟨M.Dart, M.finite, M.decEq, M.map.ecpAMap M.point, M.map.ecpAPoint M.point⟩

/-- The `R'` step: rotate the reference dart one step backwards. -/
noncomputable def ecpR' (M : PointedMap) : PointedMap :=
  M.ecpR (Function.minimalPeriod M.map.node M.point - 1)

/-- The `Y` step: a new Y junction and a new face. -/
noncomputable def ecpY (M : PointedMap) : PointedMap := M.ecpU.ecpN

/-- The `H` step: a new H junction, closing an inner face. -/
noncomputable def ecpH (M : PointedMap) : PointedMap := M.ecpY.ecpN

/-- The `K` step: a new inverted Y junction, closing off a face. -/
noncomputable def ecpK (M : PointedMap) : PointedMap := (M.ecpR'.ecpN).ecpR 1

/-- A pointed map is plain when its hypermap is. -/
def Plain (M : PointedMap) : Prop := M.map.Plain

/-- A pointed map is cubic when its hypermap is cubic away from its ring. -/
def Cubic (M : PointedMap) : Prop := M.map.Quasicubic M.cpring

end PointedMap

/-! ### Running a construction program -/

/-- The pointed map obtained by running `cp` right to left, starting from a
single edge. -/
noncomputable def cpmap : CProg → PointedMap
  | [] => PointedMap.cpmap0
  | .R n :: cp => (cpmap cp).ecpR n
  | .R' :: cp => (cpmap cp).ecpR'
  | .Y :: cp => (cpmap cp).ecpY
  | .H :: cp => (cpmap cp).ecpH
  | .U :: cp => (cpmap cp).ecpU
  | .K :: cp => (cpmap cp).ecpK
  | .A :: cp => (cpmap cp).ecpA

@[simp] theorem cpmap_nil : cpmap [] = PointedMap.cpmap0 := rfl
@[simp] theorem cpmap_R (n : ℕ) (cp : CProg) : cpmap (.R n :: cp) = (cpmap cp).ecpR n := rfl
@[simp] theorem cpmap_R' (cp : CProg) : cpmap (.R' :: cp) = (cpmap cp).ecpR' := rfl
@[simp] theorem cpmap_Y (cp : CProg) : cpmap (.Y :: cp) = (cpmap cp).ecpY := rfl
@[simp] theorem cpmap_H (cp : CProg) : cpmap (.H :: cp) = (cpmap cp).ecpH := rfl
@[simp] theorem cpmap_U (cp : CProg) : cpmap (.U :: cp) = (cpmap cp).ecpU := rfl
@[simp] theorem cpmap_K (cp : CProg) : cpmap (.K :: cp) = (cpmap cp).ecpK := rfl
@[simp] theorem cpmap_A (cp : CProg) : cpmap (.A :: cp) = (cpmap cp).ecpA := rfl


/-- The injection of the darts of `cpmap cp` into the darts of `cpmap (s :: cp)`.
The rotation and merge steps do not change the dart type, so their injections are
the identity. -/
noncomputable def injcpStep : (s : CpStep) → (cp : CProg) → (cpmap cp).Dart →
    (cpmap (s :: cp)).Dart
  | .R _, _, x => x
  | .R', _, x => x
  | .Y, _, x => .icp (.icp x)
  | .H, _, x => .icp (.icp (.icp x))
  | .U, _, x => .icp x
  | .K, _, x => .icp x
  | .A, _, x => x

/-- The one-step dart injections are injective. -/
theorem injcpStep_injective (s : CpStep) (cp : CProg) :
    Function.Injective (injcpStep s cp) := by
  intro x y h
  cases s with
  | R n => exact h
  | R' => exact h
  | Y => exact EcpDart.icp_injective (EcpDart.icp_injective h)
  | H => exact EcpDart.icp_injective (EcpDart.icp_injective (EcpDart.icp_injective h))
  | U => exact EcpDart.icp_injective h
  | K => exact EcpDart.icp_injective h
  | A => exact h

/-- A one-step dart injection commutes with `edge`, for the steps that keep the
map cubic. -/
theorem edge_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg) (x : (cpmap cp).Dart) :
    injcpStep s cp ((cpmap cp).map.edge x)
      = (cpmap (s :: cp)).map.edge (injcpStep s cp x) := by
  cases s with
  | R n => rfl
  | R' => exact hs.elim
  | Y => rfl
  | H => rfl
  | U => rfl
  | K => exact hs.elim
  | A => exact hs.elim

/-- The injection of the darts of `cpmap cp2` into the darts of the map obtained
by running `cp1` on top of `cp2`. -/
noncomputable def injcp : (cp1 cp2 : CProg) → (cpmap cp2).Dart →
    (cpmap (cp1.reverseAux cp2)).Dart
  | [], _, x => x
  | s :: cp1, cp2, x => injcp cp1 (s :: cp2) (injcpStep s cp2 x)

/-- The dart injections of a program are injective. -/
theorem injcp_injective : ∀ (cp1 cp2 : CProg), Function.Injective (injcp cp1 cp2) := by
  intro cp1
  induction cp1 with
  | nil => intro _ x y h; exact h
  | cons s cp1 ih => intro cp2 x y h; exact injcpStep_injective s cp2 (ih (s :: cp2) h)

/-- The dart injection of a cubic program commutes with `edge`. -/
theorem edge_injcp : ∀ (cp1 : CProg), CubicProg cp1 → ∀ (cp2 : CProg) (x : (cpmap cp2).Dart),
    injcp cp1 cp2 ((cpmap cp2).map.edge x)
      = (cpmap (cp1.reverseAux cp2)).map.edge (injcp cp1 cp2 x) := by
  intro cp1
  induction cp1 with
  | nil => intro _ cp2 x; rfl
  | cons s cp1 ih =>
    intro h cp2 x
    change injcp cp1 (s :: cp2) (injcpStep s cp2 ((cpmap cp2).map.edge x)) = _
    rw [edge_injcpStep h.head cp2 x]
    exact ih h.of_cons (s :: cp2) (injcpStep s cp2 x)

/-- The map of a configuration. -/
noncomputable def cfmap (cf : Config) : PointedMap := cpmap cf.prog

/-- The ring of a configuration, as an N-cycle. -/
noncomputable def cfring (cf : Config) : List (cfmap cf).Dart := (cfmap cf).cpring.reverse

/-! ### The geometry of the step constructions -/

namespace PointedMap

/-- A nontrivial ring has more than one dart. -/
theorem proper_iff (M : PointedMap) : M.Proper ↔ 1 < M.cpring.length :=
  Hypermap.proper_cpring_iff

/-- A long ring has more than two darts. -/
theorem long_iff (M : PointedMap) : M.Long ↔ 2 < M.cpring.length :=
  Hypermap.long_cpring_iff

/-- A long ring is nontrivial. -/
theorem Long.proper {M : PointedMap} (h : M.Long) : M.Proper :=
  Hypermap.LongCpring.properCpring h

/-- The ring of the initial hypermap. -/
theorem cpring_cpmap0Map : cpmap0Map.cpring true = [false, true] := by
  refine Hypermap.cpring_eq ?_ (by decide) (by simp) rfl
  refine ⟨?_, ?_⟩
  · rw [List.isChain_cons_cons]
    exact ⟨rfl, List.isChain_singleton _⟩
  · intro a ha b hb
    have ha' : a = true := by simpa using ha.symm
    have hb' : b = false := by simpa using hb.symm
    rw [ha', hb']
    rfl

/-- The ring of the initial map. -/
theorem cpring_cpmap0 : cpmap0.cpring = [false, true] := cpring_cpmap0Map

/-- The initial map has a ring of two darts. -/
@[simp] theorem length_cpring_cpmap0 : cpmap0.cpring.length = 2 := by
  rw [cpring_cpmap0]; rfl

/-- The initial ring is nontrivial. -/
theorem proper_cpmap0 : cpmap0.Proper := (proper_iff _).mpr (by simp)

/-- The initial hypermap is plain. -/
theorem plain_cpmap0Map : cpmap0Map.Plain := by
  constructor
  · intro b
    change (!(!b)) = b
    simp
  · intro b
    change (!b) ≠ b
    cases b <;> simp

/-- The initial map is plain. -/
theorem plain_cpmap0 : cpmap0.Plain := plain_cpmap0Map

/-- The initial map is cubic away from its ring, vacuously. -/
theorem cubic_cpmap0 : cpmap0.Cubic := by
  have hmem : ∀ b : Bool, b ∈ cpmap0Map.cpring true := by
    rw [cpring_cpmap0Map]
    decide
  exact ⟨fun b hb => absurd (hmem b) hb, fun b hb => absurd (hmem b) hb⟩

/-! #### Ring sizes -/

@[simp] theorem length_cpring_ecpR (n : ℕ) (M : PointedMap) :
    (M.ecpR n).cpring.length = M.cpring.length :=
  Hypermap.length_cpring_ecpR n

@[simp] theorem length_cpring_ecpU (M : PointedMap) :
    M.ecpU.cpring.length = M.cpring.length + 2 :=
  Hypermap.length_cpring_ecpU M.map M.point

/-- The ring after a `U` step is always long. -/
theorem long_ecpU (M : PointedMap) : M.ecpU.Long := Hypermap.longCpring_ecpU M.map M.point

theorem length_cpring_ecpN (M : PointedMap) (h : M.Long) :
    M.ecpN.cpring.length = M.cpring.length - 1 :=
  Hypermap.length_cpring_ecpN_of_long M.map M.point h

theorem length_cpring_ecpN_of_not_long (M : PointedMap) (h : ¬ M.Long) :
    M.ecpN.cpring.length = 1 := by
  rw [ecpN, cpring, Hypermap.cpring_ecpN_of_not_long M.map M.point h]
  rfl

@[simp] theorem length_cpring_ecpR' (M : PointedMap) :
    M.ecpR'.cpring.length = M.cpring.length := length_cpring_ecpR _ M

@[simp] theorem length_cpring_ecpY (M : PointedMap) :
    M.ecpY.cpring.length = M.cpring.length + 1 := by
  rw [ecpY, length_cpring_ecpN _ (long_ecpU M), length_cpring_ecpU]
  omega

/-- The ring after a `Y` step at a nontrivial ring is long. -/
theorem long_ecpY (M : PointedMap) (h : M.Proper) : M.ecpY.Long := by
  rw [long_iff, length_cpring_ecpY]
  have := (proper_iff M).mp h
  omega

theorem length_cpring_ecpH (M : PointedMap) (h : M.Proper) :
    M.ecpH.cpring.length = M.cpring.length := by
  rw [ecpH, length_cpring_ecpN _ (long_ecpY M h), length_cpring_ecpY]
  omega

theorem length_cpring_ecpK (M : PointedMap) (h : M.Proper) :
    M.ecpK.cpring.length = M.cpring.length - 1 := by
  have hp : M.ecpR'.Proper := by
    refine (proper_iff _).mpr ?_
    rw [length_cpring_ecpR']
    exact (proper_iff M).mp h
  rw [ecpK, length_cpring_ecpR]
  by_cases hl : M.ecpR'.Long
  · rw [length_cpring_ecpN _ hl, length_cpring_ecpR']
  · rw [length_cpring_ecpN_of_not_long _ hl]
    have h1 := (proper_iff _).mp hp
    have h2 : ¬ 2 < M.ecpR'.cpring.length := fun hc => hl ((long_iff _).mpr hc)
    rw [length_cpring_ecpR'] at h1 h2
    omega

/-! #### Plainness -/

theorem Plain.ecpR {M : PointedMap} (h : M.Plain) (n : ℕ) : (M.ecpR n).Plain := h
theorem Plain.ecpR' {M : PointedMap} (h : M.Plain) : M.ecpR'.Plain := h
theorem Plain.ecpU {M : PointedMap} (h : M.Plain) : M.ecpU.Plain :=
  Hypermap.plain_ecpU M.map M.point h
theorem Plain.ecpN {M : PointedMap} (h : M.Plain) : M.ecpN.Plain :=
  Hypermap.plain_ecpN M.map M.point h
theorem Plain.ecpY {M : PointedMap} (h : M.Plain) : M.ecpY.Plain := h.ecpU.ecpN
theorem Plain.ecpH {M : PointedMap} (h : M.Plain) : M.ecpH.Plain := h.ecpY.ecpN
theorem Plain.ecpK {M : PointedMap} (h : M.Plain) : M.ecpK.Plain := (h.ecpR'.ecpN).ecpR 1

/-! #### Cubicity -/

theorem Cubic.ecpR {M : PointedMap} (h : M.Cubic) (n : ℕ) : (M.ecpR n).Cubic :=
  Hypermap.quasicubic_ecpR (n := n) h
theorem Cubic.ecpU {M : PointedMap} (h : M.Cubic) : M.ecpU.Cubic :=
  Hypermap.quasicubic_ecpU M.map M.point h
theorem Cubic.ecpN {M : PointedMap} (hl : M.Long) (h : M.Cubic) : M.ecpN.Cubic :=
  Hypermap.quasicubic_ecpN_of_long M.map M.point hl h
theorem Cubic.ecpY {M : PointedMap} (h : M.Cubic) : M.ecpY.Cubic :=
  Cubic.ecpN (long_ecpU M) h.ecpU
theorem Cubic.ecpH {M : PointedMap} (hp : M.Proper) (h : M.Cubic) : M.ecpH.Cubic :=
  Cubic.ecpN (long_ecpY M hp) h.ecpY

/-! #### Connectivity -/

/-- A pointed map is connected when its hypermap is. -/
def Connected (M : PointedMap) : Prop := M.map.Connected

/-- A pointed map is bridgeless when its hypermap is. -/
def Bridgeless (M : PointedMap) : Prop := M.map.Bridgeless

/-- A pointed map is planar when its hypermap is. -/
def Planar (M : PointedMap) : Prop := M.map.Planar

theorem Connected.ecpR {M : PointedMap} (h : M.Connected) (n : ℕ) :
    (M.ecpR n).Connected := h
theorem Connected.ecpR' {M : PointedMap} (h : M.Connected) : M.ecpR'.Connected := h
theorem Connected.ecpU {M : PointedMap} (h : M.Connected) : M.ecpU.Connected :=
  Hypermap.connected_ecpU M.map M.point h
theorem Connected.ecpN {M : PointedMap} (h : M.Connected) : M.ecpN.Connected :=
  Hypermap.connected_ecpN M.map M.point h
theorem Connected.ecpY {M : PointedMap} (h : M.Connected) : M.ecpY.Connected := h.ecpU.ecpN
theorem Connected.ecpH {M : PointedMap} (h : M.Connected) : M.ecpH.Connected := h.ecpY.ecpN
theorem Connected.ecpK {M : PointedMap} (h : M.Connected) : M.ecpK.Connected :=
  (h.ecpR'.ecpN).ecpR 1

/-! #### The face of the new dart after a `Y` step -/

/-- After a `Y` step the new dart lies on a face with exactly two darts. -/
theorem cface_ecpY (M : PointedMap) (u : M.ecpY.Dart) :
    M.ecpY.map.CFace .X u ↔ u = .X ∨ u = .icp .X := by
  have hlong : M.ecpU.map.node⁻¹ (.X : M.ecpU.Dart) ≠ M.ecpU.map.node .X := by
    have hl := Hypermap.longCpring_ecpU M.map M.point
    rw [Hypermap.LongCpring, Hypermap.face_edge] at hl
    exact hl
  have hb : M.ecpU.map.node⁻¹ (M.ecpU.map.node⁻¹ (.X : M.ecpU.Dart)) ≠ .X := fun hc =>
    hlong ((Hypermap.inv_inv_node_eq_iff _ _).mp hc)
  cases u with
  | X => exact ⟨fun _ => Or.inl rfl, fun _ => Equiv.Perm.SameCycle.refl _ _⟩
  | Xe =>
    have h1 : M.ecpY.map.CFace (.X : M.ecpY.Dart) .Xe
        ↔ M.ecpU.map.CFace .X (M.ecpU.map.node⁻¹ (M.ecpU.map.node⁻¹ .X)) :=
      Hypermap.cface_ecpN_Xe M.ecpU.map .X
    rw [h1]
    refine ⟨fun hc => absurd ((Hypermap.cface_ecpU M.map M.point _).mp hc) hb, ?_⟩
    rintro (hc | hc) <;> exact absurd hc (by simp)
  | icp v =>
    have h1 : M.ecpY.map.CFace (.X : M.ecpY.Dart) (.icp v) ↔ M.ecpU.map.CFace v .X :=
      Hypermap.cface_ecpN_icp M.ecpU.map .X v
    rw [h1]
    constructor
    · intro hc
      exact Or.inr (congrArg EcpDart.icp ((Hypermap.cface_ecpU M.map M.point v).mp hc.symm))
    · rintro (hc | hc)
      · exact absurd hc (by simp)
      · rw [EcpDart.icp_injective hc]
        exact Equiv.Perm.SameCycle.refl _ _

/-! #### Faces and adjacency of the composite steps -/

/-- A `Y` step does not change the face orbits of the old darts. -/
theorem cface_icpY (M : PointedMap) (x y : M.Dart) :
    M.ecpY.map.CFace (.icp (.icp x)) (.icp (.icp y)) ↔ M.map.CFace x y :=
  (Hypermap.cface_icpN M.ecpU.map .X (.icp x) (.icp y)).trans
    (Hypermap.cface_icpU M.map M.point x y)

/-- An `H` step does not change the face orbits of the old darts. -/
theorem cface_icpH (M : PointedMap) (x y : M.Dart) :
    M.ecpH.map.CFace (.icp (.icp (.icp x))) (.icp (.icp (.icp y))) ↔ M.map.CFace x y :=
  (Hypermap.cface_icpN M.ecpY.map .X (.icp (.icp x)) (.icp (.icp y))).trans
    (cface_icpY M x y)

/-- After a `Y` step no old dart lies on the face of the new dart. -/
theorem not_cface_ecpY (M : PointedMap) (x : M.Dart) :
    ¬ M.ecpY.map.CFace (.icp (.icp x)) .X := by
  intro hc
  rcases (cface_ecpY M _).mp hc.symm with h | h
  · exact absurd h (by simp)
  · exact absurd (EcpDart.icp_injective h) (by simp)

/-- A `Y` step does not change the adjacency of old darts. -/
theorem adj_icpY (M : PointedMap) (x y : M.Dart) :
    M.ecpY.map.Adj (.icp (.icp x)) (.icp (.icp y)) ↔ M.map.Adj x y := by
  have hx : ¬ M.ecpU.map.CFace (.icp x) .X := fun hc =>
    absurd ((Hypermap.cface_ecpU M.map M.point _).mp hc.symm) (by simp)
  have hy : ¬ M.ecpU.map.CFace (.icp y) .X := fun hc =>
    absurd ((Hypermap.cface_ecpU M.map M.point _).mp hc.symm) (by simp)
  rw [show M.ecpY.map.Adj (.icp (.icp x)) (.icp (.icp y)) ↔ _ from
    Hypermap.adj_icpN M.ecpU.map .X (.icp x) (.icp y)]
  constructor
  · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
    · exact (Hypermap.adj_icpU M.map M.point x y).mp h
    · exact absurd h hy
    · exact absurd h hx
  · exact fun h => Or.inl ((Hypermap.adj_icpU M.map M.point x y).mpr h)

/-- An `H` step does not change the adjacency of old darts. -/
theorem adj_icpH (M : PointedMap) (x y : M.Dart) :
    M.ecpH.map.Adj (.icp (.icp (.icp x))) (.icp (.icp (.icp y))) ↔ M.map.Adj x y := by
  rw [show M.ecpH.map.Adj (.icp (.icp (.icp x))) (.icp (.icp (.icp y))) ↔ _ from
    Hypermap.adj_icpN M.ecpY.map .X (.icp (.icp x)) (.icp (.icp y))]
  constructor
  · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
    · exact (adj_icpY M x y).mp h
    · exact absurd h (not_cface_ecpY M y)
    · exact absurd h (not_cface_ecpY M x)
  · exact fun h => Or.inl ((adj_icpY M x y).mpr h)

/-! #### The `K` step -/

/-- The reference dart after an `R'` step. -/
theorem point_ecpR' (M : PointedMap) : M.ecpR'.point = M.map.node M.point :=
  Hypermap.ecpRPoint_minimalPeriod_sub_one

/-- The map of a `K` step is the `N` step at `node x₀`. -/
theorem map_ecpK (M : PointedMap) :
    M.ecpK.map = Hypermap.ecpNMap M.map (M.map.node M.point) := by
  have h : M.ecpK.map = Hypermap.ecpNMap M.map M.ecpR'.point := rfl
  rw [h, point_ecpR']

/-- The reference dart of a `K` step. -/
theorem point_ecpK (M : PointedMap) :
    M.ecpK.point = M.ecpK.map.node⁻¹ (.X : M.ecpK.Dart) := by
  have h : M.ecpK.point = ((M.ecpK.map.node⁻¹) ^ 1) (.X : M.ecpK.Dart) := rfl
  rw [h, pow_one]

/-- The node image of the reference dart of a `K` step is the new dart. -/
theorem node_point_ecpK (M : PointedMap) : M.ecpK.map.node M.ecpK.point = .X := by
  have h : M.ecpK.map.node M.ecpK.point
      = M.ecpK.map.node (M.ecpK.map.node⁻¹ (.X : M.ecpK.Dart)) := by rw [point_ecpK]
  rw [h]
  exact Hypermap.node_inv_node M.ecpK.map .X

/-- A `K` step does not change the face orbits of the old darts. -/
theorem cface_icpK (M : PointedMap) (x y : M.Dart) :
    M.ecpK.map.CFace (.icp x) (.icp y) ↔ M.map.CFace x y :=
  Hypermap.cface_icpN M.map M.ecpR'.point x y

/-- Adjacency after a `K` step: the face of `edge x₀` and the face of `node x₀`
become adjacent. -/
theorem adj_icpK (M : PointedMap) (x y : M.Dart) :
    M.ecpK.map.Adj (.icp x) (.icp y) ↔
      M.map.Adj x y
        ∨ (M.map.CFace x (M.map.node⁻¹ M.point) ∧ M.map.CFace y (M.map.node M.point))
        ∨ (M.map.CFace x (M.map.node M.point) ∧ M.map.CFace y (M.map.node⁻¹ M.point)) := by
  have hb : M.map.node⁻¹ (M.map.node⁻¹ M.ecpR'.point) = M.map.node⁻¹ M.point := by
    rw [point_ecpR', Hypermap.inv_node_node]
  have h := Hypermap.adj_icpN M.map M.ecpR'.point x y
  rw [hb, point_ecpR'] at h
  rw [map_ecpK]
  exact h

/-- A `K` step preserves adjacency of old darts. -/
theorem sub_adj_icpK (M : PointedMap) {x y : M.Dart} (h : M.map.Adj x y) :
    M.ecpK.map.Adj (.icp x) (.icp y) := (adj_icpK M x y).mpr (Or.inl h)

/-- Every dart of a `K` step map lies on the face of an old dart. -/
theorem fband_icpK (M : PointedMap) (u : M.ecpK.Dart) :
    ∃ x : M.Dart, M.ecpK.map.CFace u (.icp x) :=
  Hypermap.fband_icpN M.map M.ecpR'.point u

/-- After a `K` step the new dart lies on the face of `node x₀`. -/
theorem cface_node_ecpK (M : PointedMap) :
    M.ecpK.map.CFace (.X : M.ecpK.Dart) (.icp (M.map.node M.point)) := by
  have h := Hypermap.cface_ecpN M.map M.ecpR'.point
  rw [point_ecpR'] at h
  rw [map_ecpK]
  exact h

/-- After a `K` step the reference dart lies on the face of `node⁻¹ x₀`. -/
theorem cface_ecpK (M : PointedMap) :
    M.ecpK.map.CFace M.ecpK.point (.icp (M.map.node⁻¹ M.point)) := by
  have h := Hypermap.cface_inv_node_ecpN M.map M.ecpR'.point
  rw [point_ecpR', Hypermap.inv_node_node] at h
  rw [point_ecpK, map_ecpK]
  exact h

/-- An `H` step never changes the size of the ring. -/
theorem length_cpring_ecpH_all (M : PointedMap) :
    M.ecpH.cpring.length = M.cpring.length := by
  by_cases h : M.Proper
  · exact length_cpring_ecpH M h
  · have h1 : ¬ 1 < M.cpring.length := fun hc => h ((proper_iff M).mpr hc)
    have hpos : 0 < M.cpring.length := Hypermap.length_cpring_pos
    have hlen : M.cpring.length = 1 := by omega
    have hY : M.ecpY.cpring.length = 2 := by rw [length_cpring_ecpY, hlen]
    have hnl : ¬ M.ecpY.Long := by
      intro hc
      have h2 := (long_iff _).mp hc
      omega
    rw [ecpH, length_cpring_ecpN_of_not_long _ hnl, hlen]

/-! #### Ring sizes of the `A` and `K` steps -/

/-- An `A` step removes two darts from the ring, unless it had at most two. -/
theorem length_cpring_ecpA (M : PointedMap) :
    M.ecpA.cpring.length
      = if 2 < M.cpring.length then M.cpring.length - 2 else M.cpring.length :=
  Hypermap.length_cpring_ecpA M.map M.point

/-- A `K` step removes one dart from the ring, or leaves a single dart. -/
theorem length_cpring_ecpK_sub2 (M : PointedMap) :
    M.ecpK.cpring.length = M.cpring.length - 2 + 1 := by
  rw [ecpK, length_cpring_ecpR]
  by_cases hl : M.ecpR'.Long
  · have h := (long_iff _).mp hl
    rw [length_cpring_ecpR'] at h
    rw [length_cpring_ecpN _ hl, length_cpring_ecpR']
    omega
  · have h : ¬ 2 < M.ecpR'.cpring.length := fun hc => hl ((long_iff _).mpr hc)
    rw [length_cpring_ecpR'] at h
    rw [length_cpring_ecpN_of_not_long _ hl]
    omega

/-- The ring after a `K` step. -/
theorem cpring_ecpK (M : PointedMap) (h : M.Proper) :
    M.ecpK.cpring = .X :: (M.cpring.drop 2).map EcpDart.icp := by
  have hK := Hypermap.cpring_ecpK M.map M.point h
  have hpt : M.ecpK.point = M.ecpK.map.node⁻¹ (.X : M.ecpK.Dart) := point_ecpK M
  have hmap : M.ecpK.map = Hypermap.ecpNMap M.map (M.map.node M.point) := map_ecpK M
  have hcp : M.ecpK.cpring = M.ecpK.map.cpring M.ecpK.point := rfl
  rw [hcp, hpt, hmap]
  exact hK

/-! #### Faces and rings of the composite steps, continued -/

/-- The ring after an `A` step at a long ring. -/
theorem cpring_ecpA_of_long (M : PointedMap) (h : M.Long) :
    M.ecpA.cpring = M.cpring.drop 2 :=
  Hypermap.cpring_ecpA_of_long M.map M.point h

/-- The ring after an `A` step at a short ring. -/
theorem cpring_ecpA_of_not_long (M : PointedMap) (h : ¬ M.Long) :
    M.ecpA.cpring = M.cpring :=
  Hypermap.cpring_ecpA_of_not_long M.map M.point h

/-- The node image of the new dart after a `Y` step. -/
theorem node_ecpY (M : PointedMap) : M.ecpY.map.node (.X : M.ecpY.Dart) = .icp .Xe :=
  Hypermap.node_ecpY_X M.map M.point

/-- After a `Y` step the dart on the node of the new dart lies on the face of
`node x₀`. -/
theorem cface_icpXe_ecpY (M : PointedMap) :
    M.ecpY.map.CFace (.icp .Xe) (.icp (.icp (M.map.node M.point))) :=
  (Hypermap.cface_icpN M.ecpU.map .X .Xe (.icp (M.map.node M.point))).mpr
    ((Hypermap.cface_Xe_icpU M.map M.point (M.map.node M.point)).mpr
      (Equiv.Perm.SameCycle.refl _ _))

/-- After a `Y` step the node of the new dart lies on the face of `node x₀`. -/
theorem cface_node_ecpY (M : PointedMap) :
    M.ecpY.map.CFace (M.ecpY.map.node .X) (.icp (.icp (M.map.node M.point))) := by
  rw [node_ecpY]
  exact cface_icpXe_ecpY M

/-- The node image of the new dart after an `H` step. -/
theorem node_ecpH (M : PointedMap) (h : M.Proper) :
    M.ecpH.map.node (.X : M.ecpH.Dart) = .icp (.icp .Xe) := by
  have hl : M.ecpY.map.LongCpring (.X : M.ecpY.Dart) := long_ecpY M h
  have hn : M.ecpH.map.node (.X : M.ecpH.Dart) = .icp (M.ecpY.map.node .X) :=
    Hypermap.ecpNNode_X_of_long M.ecpY.map .X hl
  rw [hn, node_ecpY]

/-- After an `H` step the node of the new dart lies on the face of `node x₀`. -/
theorem cface_node_ecpH (M : PointedMap) (h : M.Proper) :
    M.ecpH.map.CFace (M.ecpH.map.node .X) (.icp (.icp (.icp (M.map.node M.point)))) := by
  rw [node_ecpH M h]
  exact (Hypermap.cface_icpN M.ecpY.map .X (.icp .Xe)
    (.icp (.icp (M.map.node M.point)))).mpr (cface_icpXe_ecpY M)

/-- Every dart of a `Y` step map lies on the face of an old dart, or on the new
face. -/
theorem fband_icpY (M : PointedMap) (u : M.ecpY.Dart) :
    (∃ x : M.Dart, M.ecpY.map.CFace u (.icp (.icp x))) ∨ M.ecpY.map.CFace .X u := by
  obtain ⟨v, hv⟩ := Hypermap.fband_icpN M.ecpU.map .X u
  rcases Hypermap.fband_icpU M.map M.point v with ⟨x, hx⟩ | hX
  · exact Or.inl ⟨x, hv.trans ((Hypermap.cface_icpN M.ecpU.map .X v (.icp x)).mpr hx)⟩
  · refine Or.inr ?_
    have h1 : M.ecpY.map.CFace (.X : M.ecpY.Dart) (.icp .X) :=
      Hypermap.cface_ecpN M.ecpU.map .X
    have h2 : M.ecpY.map.CFace (.icp (.X : M.ecpU.Dart)) (.icp v) :=
      (Hypermap.cface_icpN M.ecpU.map .X .X v).mpr hX
    exact (h1.trans h2).trans hv.symm

/-- Every dart of an `H` step map lies on the face of an old dart, or on the new
face. -/
theorem fband_icpH (M : PointedMap) (u : M.ecpH.Dart) :
    (∃ x : M.Dart, M.ecpH.map.CFace u (.icp (.icp (.icp x)))) ∨ M.ecpH.map.CFace .X u := by
  obtain ⟨v, hv⟩ := Hypermap.fband_icpN M.ecpY.map .X u
  rcases fband_icpY M v with ⟨x, hx⟩ | hX
  · exact Or.inl ⟨x, hv.trans
      ((Hypermap.cface_icpN M.ecpY.map .X v (.icp (.icp x))).mpr hx)⟩
  · refine Or.inr ?_
    have h1 : M.ecpH.map.CFace (.X : M.ecpH.Dart) (.icp .X) :=
      Hypermap.cface_ecpN M.ecpY.map .X
    have h2 : M.ecpH.map.CFace (.icp (.X : M.ecpY.Dart)) (.icp v) :=
      (Hypermap.cface_icpN M.ecpY.map .X .X v).mpr hX
    exact (h1.trans h2).trans hv.symm

/-- After an `H` step at a nontrivial ring the new dart lies on a face with
three darts. -/
theorem cface_ecpH (M : PointedMap) (h : M.Proper) (u : M.ecpH.Dart) :
    M.ecpH.map.CFace .X u ↔ u = .X ∨ u = .icp .X ∨ u = .icp (.icp .X) := by
  cases u with
  | X => exact ⟨fun _ => Or.inl rfl, fun _ => Equiv.Perm.SameCycle.refl _ _⟩
  | Xe =>
    have hl : M.ecpY.map.LongCpring (.X : M.ecpY.Dart) := long_ecpY M h
    have hb : M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ (.X : M.ecpY.Dart)) ≠ .X := fun hc =>
      Hypermap.longCpring_iff_inv_ne.mp hl
        ((Hypermap.inv_inv_node_eq_iff M.ecpY.map .X).mp hc)
    have hbb : M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ (.X : M.ecpY.Dart)) ≠ .icp .X := by
      intro hc
      have e1 : M.ecpY.map.node (.icp (.X : M.ecpU.Dart)) = .Xe := rfl
      have e2 : M.ecpY.map.node (.Xe : M.ecpY.Dart) = .icp (M.ecpU.map.node⁻¹ .X) := rfl
      have hs1 := Equiv.Perm.inv_eq_iff_eq.mp hc
      rw [e1] at hs1
      have hs2 := Equiv.Perm.inv_eq_iff_eq.mp hs1
      rw [e2] at hs2
      exact absurd hs2 (by simp)
    have h1 : M.ecpH.map.CFace (.X : M.ecpH.Dart) .Xe
        ↔ M.ecpY.map.CFace .X (M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ .X)) :=
      Hypermap.cface_ecpN_Xe M.ecpY.map .X
    rw [h1]
    refine ⟨fun hc => ?_, ?_⟩
    · rcases (cface_ecpY M _).mp hc with hc' | hc'
      · exact absurd hc' hb
      · exact absurd hc' hbb
    · rintro (hc | hc | hc) <;> exact absurd hc (by simp)
  | icp v =>
    have h1 : M.ecpH.map.CFace (.X : M.ecpH.Dart) (.icp v) ↔ M.ecpY.map.CFace v .X :=
      Hypermap.cface_ecpN_icp M.ecpY.map .X v
    rw [h1]
    constructor
    · intro hc
      rcases (cface_ecpY M v).mp hc.symm with hc' | hc'
      · exact Or.inr (Or.inl (congrArg EcpDart.icp hc'))
      · exact Or.inr (Or.inr (congrArg EcpDart.icp hc'))
    · rintro (hc | hc | hc)
      · exact absurd hc (by simp)
      · rw [EcpDart.icp_injective hc]
        exact ((cface_ecpY M _).mpr (Or.inl rfl)).symm
      · rw [EcpDart.icp_injective hc]
        exact ((cface_ecpY M _).mpr (Or.inr rfl)).symm

/-! #### The dart injections of the construction steps

Named injections, so that the lists of darts built below have the dart type of
the extended map rather than an unfolded `EcpDart` tower. -/

/-- The dart injection of a `U` step. -/
def icpU (M : PointedMap) (x : M.Dart) : M.ecpU.Dart := .icp x

/-- The dart injection of an `N` step. -/
def icpN (M : PointedMap) (x : M.Dart) : M.ecpN.Dart := .icp x

/-- The dart injection of a `Y` step. -/
def icpY (M : PointedMap) (x : M.Dart) : M.ecpY.Dart := .icp (.icp x)

/-- The dart injection of an `H` step. -/
def icpH (M : PointedMap) (x : M.Dart) : M.ecpH.Dart := .icp (.icp (.icp x))

/-- The `U` injection is injective. -/
theorem icpU_injective (M : PointedMap) : Function.Injective M.icpU :=
  fun _ _ h => EcpDart.icp_injective h

/-- The `Y` injection is injective. -/
theorem icpY_injective (M : PointedMap) : Function.Injective M.icpY :=
  fun _ _ h => EcpDart.icp_injective (EcpDart.icp_injective h)

/-- The `H` injection is injective. -/
theorem icpH_injective (M : PointedMap) : Function.Injective M.icpH :=
  fun _ _ h => EcpDart.icp_injective (EcpDart.icp_injective (EcpDart.icp_injective h))

/-- A `Y` step does not change face orbits, in terms of `icpY`. -/
theorem cface_icpY' (M : PointedMap) (x y : M.Dart) :
    M.ecpY.map.CFace (M.icpY x) (M.icpY y) ↔ M.map.CFace x y := cface_icpY M x y

/-- An `H` step does not change face orbits, in terms of `icpH`. -/
theorem cface_icpH' (M : PointedMap) (x y : M.Dart) :
    M.ecpH.map.CFace (M.icpH x) (M.icpH y) ↔ M.map.CFace x y := cface_icpH M x y

/-- A `Y` step does not change adjacency, in terms of `icpY`. -/
theorem adj_icpY' (M : PointedMap) (x y : M.Dart) :
    M.ecpY.map.Adj (M.icpY x) (M.icpY y) ↔ M.map.Adj x y := adj_icpY M x y

/-- An `H` step does not change adjacency, in terms of `icpH`. -/
theorem adj_icpH' (M : PointedMap) (x y : M.Dart) :
    M.ecpH.map.Adj (M.icpH x) (M.icpH y) ↔ M.map.Adj x y := adj_icpH M x y

/-- The face cover of a `Y` step, in terms of `icpY`. -/
theorem fband_icpY' (M : PointedMap) (u : M.ecpY.Dart) :
    (∃ x : M.Dart, M.ecpY.map.CFace u (M.icpY x)) ∨ M.ecpY.map.CFace .X u := fband_icpY M u

/-- The face cover of an `H` step, in terms of `icpH`. -/
theorem fband_icpH' (M : PointedMap) (u : M.ecpH.Dart) :
    (∃ x : M.Dart, M.ecpH.map.CFace u (M.icpH x)) ∨ M.ecpH.map.CFace .X u := fband_icpH M u

/-- The node of the new dart of a `Y` step, in terms of `icpY`. -/
theorem cface_node_ecpY' (M : PointedMap) :
    M.ecpY.map.CFace (M.ecpY.map.node .X) (M.icpY (M.map.node M.point)) := cface_node_ecpY M

/-- The node of the new dart of an `H` step, in terms of `icpH`. -/
theorem cface_node_ecpH' (M : PointedMap) (h : M.Proper) :
    M.ecpH.map.CFace (M.ecpH.map.node .X) (M.icpH (M.map.node M.point)) :=
  cface_node_ecpH M h

/-- The new face of a `Y` step is not the face of an old dart. -/
theorem not_cface_ecpY_icpY (M : PointedMap) (x : M.Dart) :
    ¬ M.ecpY.map.CFace (.X : M.ecpY.Dart) (M.icpY x) := fun hc => not_cface_ecpY M x hc.symm

/-- The new face of an `H` step is not the face of an old dart. -/
theorem not_cface_ecpH_icpH (M : PointedMap) (h : M.Proper) (x : M.Dart) :
    ¬ M.ecpH.map.CFace (.X : M.ecpH.Dart) (M.icpH x) := by
  intro hc
  have hx : M.icpH x = (.icp (.icp (.icp x)) : M.ecpH.Dart) := rfl
  rw [hx] at hc
  rcases (cface_ecpH M h _).mp hc with h1 | h1 | h1
  · exact absurd h1 (by simp)
  · exact absurd (EcpDart.icp_injective h1) (by simp)
  · exact absurd (EcpDart.icp_injective (EcpDart.icp_injective h1)) (by simp)

/-- The faces adjacent to the new face of a `Y` step. -/
theorem adj_ecpY (M : PointedMap) (h : M.Proper) (u : M.ecpY.Dart) :
    M.ecpY.map.Adj .X u ↔ M.ecpY.map.CFace u (M.icpY (M.map.node M.point))
      ∨ M.ecpY.map.CFace u (M.icpY M.point) := Hypermap.adj_ecpY M.map M.point h u

/-- The faces adjacent to the new face of an `H` step. -/
theorem adj_ecpH (M : PointedMap) (h : M.Proper) (u : M.ecpH.Dart) :
    M.ecpH.map.Adj .X u ↔ M.ecpH.map.CFace u (M.icpH (M.map.node M.point))
      ∨ M.ecpH.map.CFace u (M.icpH M.point)
      ∨ M.ecpH.map.CFace u (M.icpH (M.map.node⁻¹ M.point)) :=
  Hypermap.adj_ecpH M.map M.point h u

/-! #### The rings of the composite steps -/

/-- The ring after a `U` step, in terms of `icpU`. -/
theorem cpring_ecpU' (M : PointedMap) :
    M.ecpU.cpring = .Xe :: .X :: M.cpring.map M.icpU := Hypermap.cpring_ecpU M.map M.point

/-- The ring after an `N` step at a long ring, in terms of `icpN`. -/
theorem cpring_ecpN' (M : PointedMap) (h : M.Long) :
    M.ecpN.cpring = M.icpN (M.map.node M.point) :: .X :: (M.cpring.drop 3).map M.icpN :=
  Hypermap.cpring_ecpN_of_long M.map M.point h

/-- **The ring after a `Y` step**: the node of the new dart, the new dart, and
the old ring without its head. -/
theorem cpring_ecpY' (M : PointedMap) :
    M.ecpY.cpring = M.ecpY.map.node .X :: .X :: M.cpring.tail.map M.icpY := by
  have hlong : M.ecpU.Long := Hypermap.longCpring_ecpU M.map M.point
  have hhead : M.ecpU.icpN (M.ecpU.map.node (.X : M.ecpU.Dart)) = M.ecpY.map.node .X := by
    rw [node_ecpY]
    rfl
  have htail : (M.ecpU.cpring.drop 3).map M.ecpU.icpN = M.cpring.tail.map M.icpY := by
    rw [cpring_ecpU']
    rcases hcp : M.cpring with _ | ⟨a, t⟩
    · rfl
    · exact List.map_map
  have h1 : M.ecpY.cpring
      = M.ecpU.icpN (M.ecpU.map.node .X) :: .X :: ((M.ecpU.cpring.drop 3).map M.ecpU.icpN) :=
    cpring_ecpN' M.ecpU hlong
  rw [h1, hhead, htail]
  rfl

/-- **The ring after an `H` step**: the node of the new dart, the new dart, and
the old ring without its first two darts. -/
theorem cpring_ecpH' (M : PointedMap) (h : M.Proper) :
    M.ecpH.cpring = M.ecpH.map.node .X :: .X :: (M.cpring.drop 2).map M.icpH := by
  have hlong : M.ecpY.Long := long_ecpY M h
  have hhead : M.ecpY.icpN (M.ecpY.map.node (.X : M.ecpY.Dart)) = M.ecpH.map.node .X := by
    rw [node_ecpH M h, node_ecpY]
    rfl
  have hdd : M.cpring.drop 2 = M.cpring.tail.drop 1 := by
    rw [← List.drop_one, List.drop_drop]
  have htail : (M.ecpY.cpring.drop 3).map M.ecpY.icpN = (M.cpring.drop 2).map M.icpH := by
    rw [cpring_ecpY', hdd]
    rcases hct : M.cpring.tail with _ | ⟨a, t⟩
    · rfl
    · exact List.map_map
  have h1 : M.ecpH.cpring
      = M.ecpY.icpN (M.ecpY.map.node .X) :: .X :: ((M.ecpY.cpring.drop 3).map M.ecpY.icpN) :=
    cpring_ecpN' M.ecpY hlong
  rw [h1, hhead, htail]
  rfl

/-! #### Bridgelessness -/

theorem Bridgeless.ecpR {M : PointedMap} (h : M.Bridgeless) (n : ℕ) :
    (M.ecpR n).Bridgeless := h
theorem Bridgeless.ecpR' {M : PointedMap} (h : M.Bridgeless) : M.ecpR'.Bridgeless := h
theorem Bridgeless.ecpU {M : PointedMap} (h : M.Bridgeless) : M.ecpU.Bridgeless :=
  Hypermap.bridgeless_ecpU M.map M.point h

/-- A `Y` step preserves bridgelessness: the new edge joins the new face to the
face of `node x₀`. -/
theorem Bridgeless.ecpY {M : PointedMap} (h : M.Bridgeless) : M.ecpY.Bridgeless := by
  refine Hypermap.bridgeless_ecpN M.ecpU.map .X h.ecpU ?_
  intro hc
  have hb := (Hypermap.cface_ecpU M.map M.point _).mp hc
  have hl := Hypermap.longCpring_ecpU M.map M.point
  rw [Hypermap.LongCpring, Hypermap.face_edge] at hl
  exact hl ((Hypermap.inv_inv_node_eq_iff _ _).mp hb)

/-- An `H` step at a nontrivial ring preserves bridgelessness. -/
theorem Bridgeless.ecpH {M : PointedMap} (hp : M.Proper) (h : M.Bridgeless) :
    M.ecpH.Bridgeless := by
  refine Hypermap.bridgeless_ecpN M.ecpY.map .X h.ecpY ?_
  intro hc
  have hb := (cface_ecpY M _).mp hc
  have hl := long_ecpY M hp
  rw [Long, Hypermap.LongCpring, Hypermap.face_edge] at hl
  rcases hb with hb | hb
  · exact hl ((Hypermap.inv_inv_node_eq_iff _ _).mp hb)
  · have e1 : M.ecpY.map.node (.icp (.X : M.ecpU.Dart)) = .Xe := rfl
    have e2 : M.ecpY.map.node (.Xe : M.ecpY.Dart) = .icp (M.ecpU.map.node⁻¹ .X) := rfl
    have hs1 := Equiv.Perm.inv_eq_iff_eq.mp hb
    rw [e1] at hs1
    have hs2 := Equiv.Perm.inv_eq_iff_eq.mp hs1
    rw [e2] at hs2
    exact absurd hs2 (by simp)

/-! #### Planarity -/

theorem Planar.ecpR {M : PointedMap} (h : M.Planar) (n : ℕ) : (M.ecpR n).Planar := h
theorem Planar.ecpR' {M : PointedMap} (h : M.Planar) : M.ecpR'.Planar := h

theorem Planar.ecpU {M : PointedMap} (hplain : M.Plain) (hcubic : M.Cubic)
    (hconn : M.Connected) (h : M.Planar) : M.ecpU.Planar :=
  Hypermap.planar_ecpU M.map M.point hplain hcubic hconn h

theorem Planar.ecpN {M : PointedMap} (hlong : M.Long) (hplain : M.Plain)
    (hcubic : M.Cubic) (hconn : M.Connected) (h : M.Planar) : M.ecpN.Planar :=
  Hypermap.planar_ecpN M.map M.point hlong hplain hcubic hconn h

theorem Planar.ecpY {M : PointedMap} (hplain : M.Plain) (hcubic : M.Cubic)
    (hconn : M.Connected) (h : M.Planar) : M.ecpY.Planar :=
  Planar.ecpN (long_ecpU M) hplain.ecpU hcubic.ecpU hconn.ecpU
    (Planar.ecpU hplain hcubic hconn h)

theorem Planar.ecpH {M : PointedMap} (hp : M.Proper) (hplain : M.Plain)
    (hcubic : M.Cubic) (hconn : M.Connected) (h : M.Planar) : M.ecpH.Planar :=
  Planar.ecpN (long_ecpY M hp) hplain.ecpY hcubic.ecpY hconn.ecpY
    (Planar.ecpY hplain hcubic hconn h)

/-! #### The initial map -/

/-- The initial map is connected. -/
theorem connected_cpmap0 : cpmap0.Connected := by
  refine Hypermap.connected_of_forall_eqvGen _ true fun b => ?_
  cases b with
  | true => exact Relation.EqvGen.refl _
  | false => exact Relation.EqvGen.rel _ _ (Or.inl rfl)

/-- The face map of the initial map is the identity. -/
theorem face_cpmap0Map : cpmap0Map.face = 1 := Equiv.ext fun _ => rfl

/-- The initial map is bridgeless. -/
theorem bridgeless_cpmap0 : cpmap0.Bridgeless := by
  intro b hb
  obtain ⟨i, hi⟩ := hb
  have hi' : (cpmap0Map.face ^ i) b = cpmap0Map.edge b := hi
  rw [face_cpmap0Map, one_zpow] at hi'
  have he : cpmap0Map.edge b = !b := rfl
  rw [he] at hi'
  cases b <;> simp at hi'

/-- The initial map has two faces. -/
theorem cycleCount_face_cpmap0 : cycleCount cpmap0Map.face = 2 := by
  rw [face_cpmap0Map, cycleCount_one]
  simp

/-- The initial map is planar. -/
theorem planar_cpmap0 : cpmap0.Planar := by
  have hgeo := Hypermap.ucyclePlainQuasicubicConnected_of cpmap0Map true plain_cpmap0Map
    cubic_cpmap0 connected_cpmap0
  refine (Hypermap.quasicubic_Euler hgeo (Hypermap.reverse_cpring_ne_nil _ _)).mpr ?_
  rw [List.length_reverse, cycleCount_face_cpmap0]
  have hlen : (cpmap0Map.cpring true).length = 2 := length_cpring_cpmap0
  rw [hlen]
  simp

end PointedMap

/-! ### The geometry of the map of a program -/

/-- The size of the ring of `cpmap cp`.  The `A` step shortens the ring by two
darts, except on rings of at most two darts. -/
def sub2ifgt2 (n : ℕ) : ℕ := if 2 < n then n - 2 else n

/-- The size of the ring of `cpmap cp`. -/
def cprsize : CProg → ℕ
  | [] => 2
  | .R _ :: cp => cprsize cp
  | .R' :: cp => cprsize cp
  | .Y :: cp => cprsize cp + 1
  | .H :: cp => cprsize cp
  | .U :: cp => cprsize cp + 2
  | .K :: cp => cprsize cp - 2 + 1
  | .A :: cp => sub2ifgt2 (cprsize cp)

/-- The number of kernel faces of `cpmap cp`. -/
def cpksize : CProg → ℕ
  | [] => 0
  | .R _ :: cp => cpksize cp
  | .R' :: cp => cpksize cp
  | .Y :: cp => cpksize cp
  | .H :: cp => cpksize cp + 1
  | .U :: cp => cpksize cp
  | .K :: cp => cpksize cp
  | .A :: cp => cpksize cp

/-- The map of a cubic program has a nontrivial ring. -/
theorem cpmap_proper : ∀ {cp : CProg}, CubicProg cp → (cpmap cp).Proper := by
  intro cp
  induction cp with
  | nil => intro _; exact PointedMap.proper_cpmap0
  | cons s cp ih =>
    intro h
    have hcp := ih h.of_cons
    have hs := h.head
    have hlen := (PointedMap.proper_iff _).mp hcp
    cases s with
    | R n => exact (PointedMap.proper_iff _).mpr (by simpa using hlen)
    | R' => exact hs.elim
    | Y =>
      refine (PointedMap.proper_iff _).mpr ?_
      rw [cpmap_Y, PointedMap.length_cpring_ecpY]
      omega
    | H =>
      refine (PointedMap.proper_iff _).mpr ?_
      rw [cpmap_H, PointedMap.length_cpring_ecpH _ hcp]
      omega
    | U =>
      refine (PointedMap.proper_iff _).mpr ?_
      rw [cpmap_U, PointedMap.length_cpring_ecpU]
      omega
    | K => exact hs.elim
    | A => exact hs.elim

/-- The map of a cubic program is plain. -/
theorem cpmap_plain : ∀ {cp : CProg}, CubicProg cp → (cpmap cp).Plain := by
  intro cp
  induction cp with
  | nil => intro _; exact PointedMap.plain_cpmap0
  | cons s cp ih =>
    intro h
    have hcp := ih h.of_cons
    have hs := h.head
    cases s with
    | R n => exact hcp.ecpR n
    | R' => exact hs.elim
    | Y => exact hcp.ecpY
    | H => exact hcp.ecpH
    | U => exact hcp.ecpU
    | K => exact hs.elim
    | A => exact hs.elim

/-- The map of a cubic program is cubic away from its ring. -/
theorem cpmap_cubic : ∀ {cp : CProg}, CubicProg cp → (cpmap cp).Cubic := by
  intro cp
  induction cp with
  | nil => intro _; exact PointedMap.cubic_cpmap0
  | cons s cp ih =>
    intro h
    have hcp := ih h.of_cons
    have hs := h.head
    cases s with
    | R n => exact hcp.ecpR n
    | R' => exact hs.elim
    | Y => exact hcp.ecpY
    | H => exact PointedMap.Cubic.ecpH (cpmap_proper h.of_cons) hcp
    | U => exact hcp.ecpU
    | K => exact hs.elim
    | A => exact hs.elim

/-- The ring of the map of a program has the predicted size. -/
theorem size_ring_cpmap : ∀ (cp : CProg), (cpmap cp).cpring.length = cprsize cp := by
  intro cp
  induction cp with
  | nil => simp [cprsize]
  | cons s cp ih =>
    cases s with
    | R n => rw [cpmap_R, PointedMap.length_cpring_ecpR, ih]; rfl
    | R' => rw [cpmap_R', PointedMap.length_cpring_ecpR', ih]; rfl
    | Y => rw [cpmap_Y, PointedMap.length_cpring_ecpY, ih]; rfl
    | H => rw [cpmap_H, PointedMap.length_cpring_ecpH_all, ih]; rfl
    | U => rw [cpmap_U, PointedMap.length_cpring_ecpU, ih]; rfl
    | K => rw [cpmap_K, PointedMap.length_cpring_ecpK_sub2, ih]; rfl
    | A =>
      rw [cpmap_A, PointedMap.length_cpring_ecpA, ih]
      rfl

/-- The map of a cubic program is connected. -/
theorem cpmap_connected : ∀ {cp : CProg}, CubicProg cp → (cpmap cp).Connected := by
  intro cp
  induction cp with
  | nil => intro _; exact PointedMap.connected_cpmap0
  | cons s cp ih =>
    intro h
    have hcp := ih h.of_cons
    have hs := h.head
    cases s with
    | R n => exact hcp.ecpR n
    | R' => exact hs.elim
    | Y => exact hcp.ecpY
    | H => exact hcp.ecpH
    | U => exact hcp.ecpU
    | K => exact hs.elim
    | A => exact hs.elim

/-- The map of a cubic program is bridgeless. -/
theorem cpmap_bridgeless : ∀ {cp : CProg}, CubicProg cp → (cpmap cp).Bridgeless := by
  intro cp
  induction cp with
  | nil => intro _; exact PointedMap.bridgeless_cpmap0
  | cons s cp ih =>
    intro h
    have hcp := ih h.of_cons
    have hs := h.head
    cases s with
    | R n => exact hcp.ecpR n
    | R' => exact hs.elim
    | Y => exact hcp.ecpY
    | H => exact PointedMap.Bridgeless.ecpH (cpmap_proper h.of_cons) hcp
    | U => exact hcp.ecpU
    | K => exact hs.elim
    | A => exact hs.elim

/-- The map of a cubic program is planar. -/
theorem cpmap_planar : ∀ {cp : CProg}, CubicProg cp → (cpmap cp).Planar := by
  intro cp
  induction cp with
  | nil => intro _; exact PointedMap.planar_cpmap0
  | cons s cp ih =>
    intro h
    have hcp := ih h.of_cons
    have hs := h.head
    cases s with
    | R n => exact hcp.ecpR n
    | R' => exact hs.elim
    | Y =>
      exact PointedMap.Planar.ecpY (cpmap_plain h.of_cons) (cpmap_cubic h.of_cons)
        (cpmap_connected h.of_cons) hcp
    | H =>
      exact PointedMap.Planar.ecpH (cpmap_proper h.of_cons) (cpmap_plain h.of_cons)
        (cpmap_cubic h.of_cons) (cpmap_connected h.of_cons) hcp
    | U =>
      exact PointedMap.Planar.ecpU (cpmap_plain h.of_cons) (cpmap_cubic h.of_cons)
        (cpmap_connected h.of_cons) hcp
    | K => exact hs.elim
    | A => exact hs.elim

/-- The map of a configuration program has a long ring: configuration programs
end with a `Y` step, so their map has at least three ring darts. -/
theorem cfmap_long : ∀ {cp : CProg}, ConfigProg cp → (cpmap cp).Long := by
  intro cp
  induction cp with
  | nil => intro h; exact absurd h.2 (by simp)
  | cons s cp ih =>
    intro h
    have hs := h.1 s List.mem_cons_self
    by_cases hnil : cp = []
    · subst hnil
      have hsY : s = CpStep.Y := by
        have := h.2
        simpa using this
      subst hsY
      refine (PointedMap.long_iff _).mpr ?_
      rw [cpmap_Y, PointedMap.length_cpring_ecpY, cpmap_nil,
        PointedMap.length_cpring_cpmap0]
      omega
    · have hcp := ih (h.of_cons hnil)
      have hlen := (PointedMap.long_iff _).mp hcp
      cases s with
      | R n =>
        refine (PointedMap.long_iff _).mpr ?_
        rw [cpmap_R, PointedMap.length_cpring_ecpR]
        exact hlen
      | R' => exact hs.elim
      | Y =>
        refine (PointedMap.long_iff _).mpr ?_
        rw [cpmap_Y, PointedMap.length_cpring_ecpY]
        omega
      | H =>
        refine (PointedMap.long_iff _).mpr ?_
        rw [cpmap_H, PointedMap.length_cpring_ecpH _ hcp.proper]
        exact hlen
      | U => exact hs.elim
      | K => exact hs.elim
      | A => exact hs.elim

/-! ### The dart injections, faces and adjacency -/

/-- A one-step dart injection preserves and reflects face orbits. -/
theorem cface_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (s :: cp)).map.CFace (injcpStep s cp x) (injcpStep s cp y)
      ↔ (cpmap cp).map.CFace x y := by
  cases s with
  | R n => exact Iff.rfl
  | R' => exact hs.elim
  | Y => exact PointedMap.cface_icpY (cpmap cp) x y
  | H => exact PointedMap.cface_icpH (cpmap cp) x y
  | U => exact Hypermap.cface_icpU (cpmap cp).map (cpmap cp).point x y
  | K => exact hs.elim
  | A => exact hs.elim

/-- A one-step dart injection preserves and reflects adjacency. -/
theorem adj_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (s :: cp)).map.Adj (injcpStep s cp x) (injcpStep s cp y)
      ↔ (cpmap cp).map.Adj x y := by
  cases s with
  | R n => exact Iff.rfl
  | R' => exact hs.elim
  | Y => exact PointedMap.adj_icpY (cpmap cp) x y
  | H => exact PointedMap.adj_icpH (cpmap cp) x y
  | U => exact Hypermap.adj_icpU (cpmap cp).map (cpmap cp).point x y
  | K => exact hs.elim
  | A => exact hs.elim

/-- The dart injection of a cubic program preserves and reflects face orbits. -/
theorem cface_injcp : ∀ (cp1 : CProg), CubicProg cp1 → ∀ (cp2 : CProg) (x y : (cpmap cp2).Dart),
    (cpmap (cp1.reverseAux cp2)).map.CFace (injcp cp1 cp2 x) (injcp cp1 cp2 y)
      ↔ (cpmap cp2).map.CFace x y := by
  intro cp1
  induction cp1 with
  | nil => intro _ _ _ _; exact Iff.rfl
  | cons s cp1 ih =>
    intro h cp2 x y
    exact (ih h.of_cons (s :: cp2) (injcpStep s cp2 x) (injcpStep s cp2 y)).trans
      (cface_injcpStep h.head cp2 x y)

/-- The dart injection of a cubic program preserves and reflects adjacency. -/
theorem adj_injcp : ∀ (cp1 : CProg), CubicProg cp1 → ∀ (cp2 : CProg) (x y : (cpmap cp2).Dart),
    (cpmap (cp1.reverseAux cp2)).map.Adj (injcp cp1 cp2 x) (injcp cp1 cp2 y)
      ↔ (cpmap cp2).map.Adj x y := by
  intro cp1
  induction cp1 with
  | nil => intro _ _ _ _; exact Iff.rfl
  | cons s cp1 ih =>
    intro h cp2 x y
    exact (ih h.of_cons (s :: cp2) (injcpStep s cp2 x) (injcpStep s cp2 y)).trans
      (adj_injcpStep h.head cp2 x y)

/-! ### The dart injections preserve faces and adjacency

Unlike `cface_injcp` and `adj_injcp`, these hold for every construction step,
including the ones that merge faces. -/

/-- A one-step dart injection preserves face orbits. -/
theorem sub_cface_injcpStep (s : CpStep) (cp : CProg) {x y : (cpmap cp).Dart}
    (h : (cpmap cp).map.CFace x y) :
    (cpmap (s :: cp)).map.CFace (injcpStep s cp x) (injcpStep s cp y) := by
  cases s with
  | R n => exact h
  | R' => exact h
  | Y => exact (PointedMap.cface_icpY (cpmap cp) x y).mpr h
  | H => exact (PointedMap.cface_icpH (cpmap cp) x y).mpr h
  | U => exact (Hypermap.cface_icpU (cpmap cp).map (cpmap cp).point x y).mpr h
  | K => exact (PointedMap.cface_icpK (cpmap cp) x y).mpr h
  | A => exact Hypermap.sub_cface_icpA (cpmap cp).map (cpmap cp).point h

/-- A one-step dart injection preserves adjacency. -/
theorem sub_adj_injcpStep (s : CpStep) (cp : CProg) {x y : (cpmap cp).Dart}
    (h : (cpmap cp).map.Adj x y) :
    (cpmap (s :: cp)).map.Adj (injcpStep s cp x) (injcpStep s cp y) := by
  cases s with
  | R n => exact h
  | R' => exact h
  | Y => exact (PointedMap.adj_icpY (cpmap cp) x y).mpr h
  | H => exact (PointedMap.adj_icpH (cpmap cp) x y).mpr h
  | U => exact (Hypermap.adj_icpU (cpmap cp).map (cpmap cp).point x y).mpr h
  | K => exact PointedMap.sub_adj_icpK (cpmap cp) h
  | A => exact Hypermap.sub_adj_icpA (cpmap cp).map (cpmap cp).point h

/-- The dart injection of any program preserves face orbits. -/
theorem sub_cface_injcp : ∀ (cp1 cp2 : CProg) {x y : (cpmap cp2).Dart},
    (cpmap cp2).map.CFace x y →
      (cpmap (cp1.reverseAux cp2)).map.CFace (injcp cp1 cp2 x) (injcp cp1 cp2 y) := by
  intro cp1
  induction cp1 with
  | nil => intro _ _ _ h; exact h
  | cons s cp1 ih =>
    intro cp2 x y h
    exact ih (s :: cp2) (sub_cface_injcpStep s cp2 h)

/-- The dart injection of any program preserves adjacency. -/
theorem sub_adj_injcp : ∀ (cp1 cp2 : CProg) {x y : (cpmap cp2).Dart},
    (cpmap cp2).map.Adj x y →
      (cpmap (cp1.reverseAux cp2)).map.Adj (injcp cp1 cp2 x) (injcp cp1 cp2 y) := by
  intro cp1
  induction cp1 with
  | nil => intro _ _ _ h; exact h
  | cons s cp1 ih =>
    intro cp2 x y h
    exact ih (s :: cp2) (sub_adj_injcpStep s cp2 h)

/-! ### The dart injections and the node structure -/

/-- Iterating `node` keeps a dart off the ring. -/
private theorem pow_node_not_mem_cpring {M : PointedMap} {x : M.Dart}
    (hx : x ∉ M.cpring) : ∀ n : ℕ, (M.map.node ^ n) x ∉ M.cpring := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact fun hc => ih (Hypermap.mem_cpring_node_iff.mp hc)

/-- A one-step dart injection commutes with `node` away from the ring. -/
theorem node_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg) {x : (cpmap cp).Dart}
    (hx : x ∉ (cpmap cp).cpring) :
    injcpStep s cp ((cpmap cp).map.node x)
      = (cpmap (s :: cp)).map.node (injcpStep s cp x) := by
  have hxn : x ≠ (cpmap cp).map.node (cpmap cp).point := fun hc =>
    hx (by rw [hc]; exact Hypermap.node_mem_cpring)
  cases s with
  | R n => rfl
  | R' => exact hs.elim
  | Y => exact (Hypermap.node_ecpY_icp (cpmap cp).map (cpmap cp).point hx).symm
  | H => exact (Hypermap.node_ecpH_icp (cpmap cp).map (cpmap cp).point hx).symm
  | U => exact (Hypermap.ecpUNode_icp_of_ne (cpmap cp).map (cpmap cp).point hxn).symm
  | K => exact hs.elim
  | A => exact hs.elim

/-- A one-step dart injection maps darts off the ring to darts off the ring. -/
theorem not_mem_cpring_injcpStep {s : CpStep} (hs : s.IsCubic) (cp : CProg)
    {x : (cpmap cp).Dart} (hx : x ∉ (cpmap cp).cpring) :
    injcpStep s cp x ∉ (cpmap (s :: cp)).cpring := by
  cases s with
  | R n => exact fun hc => hx (Hypermap.mem_cpring_ecpR.mp hc)
  | R' => exact hs.elim
  | Y => exact Hypermap.not_mem_cpring_ecpY (cpmap cp).map (cpmap cp).point hx
  | H => exact Hypermap.not_mem_cpring_ecpH (cpmap cp).map (cpmap cp).point hx
  | U =>
    exact fun hc => hx ((Hypermap.mem_cpring_ecpU_icp (cpmap cp).map (cpmap cp).point).mp hc)
  | K => exact hs.elim
  | A => exact hs.elim

/-- The dart injection of a cubic program commutes with `node` away from the
ring. -/
theorem node_injcp : ∀ (cp1 : CProg), CubicProg cp1 → ∀ (cp2 : CProg) (x : (cpmap cp2).Dart),
    x ∉ (cpmap cp2).cpring →
      injcp cp1 cp2 ((cpmap cp2).map.node x)
        = (cpmap (cp1.reverseAux cp2)).map.node (injcp cp1 cp2 x) := by
  intro cp1
  induction cp1 with
  | nil => intro _ _ _ _; rfl
  | cons s cp1 ih =>
    intro h cp2 x hx
    change injcp cp1 (s :: cp2) (injcpStep s cp2 ((cpmap cp2).map.node x)) = _
    rw [node_injcpStep h.head cp2 hx]
    exact ih h.of_cons (s :: cp2) (injcpStep s cp2 x)
      (not_mem_cpring_injcpStep h.head cp2 hx)

/-- The dart injection of a cubic program commutes with the iterates of `node`
away from the ring. -/
private theorem pow_node_injcp (cp1 : CProg) (h : CubicProg cp1) (cp2 : CProg)
    {x : (cpmap cp2).Dart} (hx : x ∉ (cpmap cp2).cpring) (n : ℕ) :
    injcp cp1 cp2 (((cpmap cp2).map.node ^ n) x)
      = ((cpmap (cp1.reverseAux cp2)).map.node ^ n) (injcp cp1 cp2 x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply, ← ih,
      node_injcp cp1 h cp2 _ (pow_node_not_mem_cpring hx n)]

/-- The dart injection of a cubic program preserves and reflects node orbits
away from the ring. -/
theorem cnode_injcp (cp1 : CProg) (h : CubicProg cp1) (cp2 : CProg) {x : (cpmap cp2).Dart}
    (hx : x ∉ (cpmap cp2).cpring) (y : (cpmap cp2).Dart) :
    (cpmap (cp1.reverseAux cp2)).map.CNode (injcp cp1 cp2 x) (injcp cp1 cp2 y)
      ↔ (cpmap cp2).map.CNode x y := by
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := (sameCycle_iff_exists_pow _ _ _).mp hxy
    rw [← pow_node_injcp cp1 h cp2 hx n] at hn
    exact (sameCycle_iff_exists_pow _ _ _).mpr ⟨n, injcp_injective cp1 cp2 hn⟩
  · intro hxy
    obtain ⟨n, hn⟩ := (sameCycle_iff_exists_pow _ _ _).mp hxy
    refine (sameCycle_iff_exists_pow _ _ _).mpr ⟨n, ?_⟩
    rw [← pow_node_injcp cp1 h cp2 hx n, hn]

/-! ### Expanding `Y` and `H` steps

A `Y` step does the same as the program `R'; K; R 1; U`, and an `H` step the
same as `R'; K; K; R 1; U`; the colouring development runs configuration
programs in this expanded form, where every step adds at most one node. -/

namespace PointedMap

/-- An `R 1` step followed by an `R'` step is the identity. -/
theorem ecpR'_ecpR_one (N : PointedMap) : (N.ecpR 1).ecpR' = N := by
  have h1 : N.map.ecpRPoint N.point 1 = N.map.node⁻¹ N.point := by
    rw [Hypermap.ecpRPoint, pow_one]
  have hm : Function.minimalPeriod N.map.node (N.map.ecpRPoint N.point 1)
      = Function.minimalPeriod N.map.node N.point := by
    rw [h1]
    have h2 := Function.minimalPeriod_apply
      (Hypermap.mem_periodicPts N.map.node (N.map.node⁻¹ N.point))
    rw [Hypermap.node_inv_node] at h2
    exact h2.symm
  have hmpos : 0 < Function.minimalPeriod N.map.node N.point :=
    minimalPeriod_pos N.map.node N.point
  have hpt : N.map.ecpRPoint (N.map.ecpRPoint N.point 1)
      (Function.minimalPeriod N.map.node (N.map.ecpRPoint N.point 1) - 1) = N.point := by
    rw [hm, Hypermap.ecpRPoint, Hypermap.ecpRPoint, ← Perm.mul_apply, ← pow_add,
      Nat.sub_add_cancel hmpos, inv_pow, Equiv.Perm.inv_eq_iff_eq]
    exact ((Hypermap.pow_node_eq_self_iff N.map N.point _).mpr dvd_rfl).symm
  have h : (N.ecpR 1).ecpR' = ⟨N.Dart, N.finite, N.decEq, N.map,
      N.map.ecpRPoint (N.map.ecpRPoint N.point 1)
        (Function.minimalPeriod N.map.node (N.map.ecpRPoint N.point 1) - 1)⟩ := rfl
  rw [h, hpt]

/-- A `Y` step is an expanded `R'; K; R 1; U`. -/
theorem ecpY_expand (M : PointedMap) : ((M.ecpU.ecpR 1).ecpK).ecpR' = M.ecpY := by
  have h1 : (M.ecpU.ecpR 1).ecpK = ((M.ecpU.ecpR 1).ecpR'.ecpN).ecpR 1 := rfl
  rw [h1, ecpR'_ecpR_one, ecpR'_ecpR_one]
  rfl

/-- An `H` step is an expanded `R'; K; K; R 1; U`. -/
theorem ecpH_expand (M : PointedMap) : (((M.ecpU.ecpR 1).ecpK).ecpK).ecpR' = M.ecpH := by
  have h1 : (M.ecpU.ecpR 1).ecpK = M.ecpY.ecpR 1 := by
    have h : (M.ecpU.ecpR 1).ecpK = ((M.ecpU.ecpR 1).ecpR'.ecpN).ecpR 1 := rfl
    rw [h, ecpR'_ecpR_one]
    rfl
  rw [h1]
  have h2 : (M.ecpY.ecpR 1).ecpK = M.ecpH.ecpR 1 := by
    have h : (M.ecpY.ecpR 1).ecpK = ((M.ecpY.ecpR 1).ecpR'.ecpN).ecpR 1 := rfl
    rw [h, ecpR'_ecpR_one]
    rfl
  rw [h2, ecpR'_ecpR_one]

end PointedMap

/-- The expansion of a single construction step. -/
def cpexpand1 : CpStep → CProg
  | .Y => [.R', .K, .R 1, .U]
  | .H => [.R', .K, .K, .R 1, .U]
  | s => [s]

/-- The expansion of a construction program: every `Y` and `H` step is replaced
by an equivalent program of `R`, `R'`, `K` and `U` steps. -/
def cpexpand : CProg → CProg
  | [] => []
  | s :: cp => cpexpand1 s ++ cpexpand cp

/-- Expanding a `Y` step does not change the map. -/
theorem cpmap_expand_Y (cp : CProg) :
    cpmap (.R' :: .K :: .R 1 :: .U :: cp) = cpmap (.Y :: cp) :=
  PointedMap.ecpY_expand (cpmap cp)

/-- Expanding an `H` step does not change the map. -/
theorem cpmap_expand_H (cp : CProg) :
    cpmap (.R' :: .K :: .K :: .R 1 :: .U :: cp) = cpmap (.H :: cp) :=
  PointedMap.ecpH_expand (cpmap cp)

/-- Expanding a `Y` step does not change the dart injection. -/
theorem injcp_expand_Y (cp : CProg) (x : (cpmap cp).Dart) :
    injcp [.U, .R 1, .K, .R'] cp x = injcpStep .Y cp x := rfl

/-- Expanding an `H` step does not change the dart injection. -/
theorem injcp_expand_H (cp : CProg) (x : (cpmap cp).Dart) :
    injcp [.U, .R 1, .K, .K, .R'] cp x = injcpStep .H cp x := rfl

/-- Expanding one step does not change the map. -/
theorem cpmap_cpexpand1 (s : CpStep) (cp : CProg) :
    cpmap (cpexpand1 s ++ cp) = cpmap (s :: cp) := by
  cases s with
  | R n => rfl
  | R' => rfl
  | Y => exact cpmap_expand_Y cp
  | H => exact cpmap_expand_H cp
  | U => rfl
  | K => rfl
  | A => rfl

/-- **Expanding a program does not change the map it builds.** -/
theorem cpmap_cpexpand : ∀ (cp1 cp2 : CProg),
    cpmap (cpexpand cp1 ++ cp2) = cpmap (cp1 ++ cp2) := by
  intro cp1
  induction cp1 with
  | nil => intro _; rfl
  | cons s cp1 ih =>
    intro cp2
    have hih := ih cp2
    rw [cpexpand, List.append_assoc, cpmap_cpexpand1]
    cases s with
    | R n => exact congrArg (PointedMap.ecpR n) hih
    | R' => exact congrArg PointedMap.ecpR' hih
    | Y => exact congrArg PointedMap.ecpY hih
    | H => exact congrArg PointedMap.ecpH hih
    | U => exact congrArg PointedMap.ecpU hih
    | K => exact congrArg PointedMap.ecpK hih
    | A => exact congrArg PointedMap.ecpA hih

/-! ### Masks selecting faces of a configuration map -/

/-- The sublist of `l` selected by the bit mask `m`. -/
def listMask {α : Type*} : List Bool → List α → List α
  | [], _ => []
  | _, [] => []
  | true :: m, x :: l => x :: listMask m l
  | false :: m, _ :: l => listMask m l

/-- A transversal of the kernel faces of `cpmap cp`: one dart for each face not
incident to the ring. -/
noncomputable def cpker : (cp : CProg) → List (cpmap cp).Dart
  | [] => []
  | .R _ :: cp => cpker cp
  | .R' :: _ => []
  | .Y :: cp => (cpker cp).map fun x => .icp (.icp x)
  | .H :: cp =>
      match ((cpmap cp).cpring)[1]? with
      | none => []
      | some x => (x :: cpker cp).map fun y => .icp (.icp (.icp y))
  | .U :: _ => []
  | .K :: _ => []
  | .A :: _ => []

/-- A pair of bit masks selecting faces of a configuration map: one for the ring
and one for the kernel. -/
structure CfMask where
  /-- The mask selecting ring faces. -/
  ring : List Bool
  /-- The mask selecting kernel faces. -/
  kernel : List Bool

/-- A mask is proper for `cp` when its two parts have the right lengths. -/
def CfMask.Proper (cm : CfMask) (cp : CProg) : Prop :=
  cm.ring.length = cprsize cp ∧ cm.kernel.length = cpksize cp

/-- The darts of `cpmap cp` selected by a mask. -/
noncomputable def cpmask (cm : CfMask) (cp : CProg) : List (cpmap cp).Dart :=
  listMask cm.ring (cpmap cp).cpring ++ listMask cm.kernel (cpker cp)

/-- The mask selecting the `i`-th kernel face of `cp`. -/
def cfmask1 (cp : CProg) (i : ℕ) : CfMask :=
  ⟨List.replicate (cprsize cp) false, (List.range (cpksize cp)).map fun j => j == i⟩

/-- The length of a mapped list, at a type that needs unfolding. -/
private theorem length_map' {α β : Type} (f : α → β) (l : List α) :
    (l.map f).length = l.length := List.length_map ..

/-- The kernel transversal of an `H` step. -/
theorem cpker_H (cp : CProg) : cpker (.H :: cp) =
    match ((cpmap cp).cpring)[1]? with
    | none => []
    | some x => (x :: cpker cp).map fun y => EcpDart.icp (.icp (.icp y)) := rfl

/-- The kernel transversal of an `H` step at a nontrivial ring. -/
theorem cpker_H_of_lt (cp : CProg) (hlen : 1 < (cpmap cp).cpring.length) :
    cpker (.H :: cp)
      = (((cpmap cp).cpring[1]'hlen) :: cpker cp).map
          fun y => EcpDart.icp (.icp (.icp y)) := by
  rw [cpker_H, List.getElem?_eq_getElem hlen]
  rfl

/-- **The size of the kernel transversal**: one dart per `H` step. -/
theorem size_cpker : ∀ {cp : CProg}, ConfigProg cp → (cpker cp).length = cpksize cp := by
  intro cp
  induction cp with
  | nil => intro h; exact absurd rfl h.ne_nil
  | cons s cp ih =>
    intro h
    have hs := h.1 s List.mem_cons_self
    cases s with
    | R n =>
      have hnil : cp ≠ [] := by
        rintro rfl
        exact absurd h.2 (by simp)
      exact ih (h.of_cons hnil)
    | R' => exact hs.elim
    | Y =>
      by_cases hnil : cp = []
      · subst hnil; rfl
      · have hih := ih (h.of_cons hnil)
        have hk : (cpker (.Y :: cp)).length = (cpker cp).length :=
          length_map' _ (cpker cp)
        rw [hk, hih]
        rfl
    | H =>
      have hnil : cp ≠ [] := by
        rintro rfl
        exact absurd h.2 (by simp)
      have hcp := h.of_cons hnil
      have hp : (cpmap cp).Proper := cpmap_proper hcp.cubicProg
      have hlen : 1 < (cpmap cp).cpring.length := (PointedMap.proper_iff _).mp hp
      have hk : (cpker (.H :: cp)).length = (cpker cp).length + 1 := by
        rw [cpker_H_of_lt cp hlen]
        exact length_map' _ ((cpmap cp).cpring[1]'hlen :: cpker cp)
      rw [hk, ih hcp]
      rfl
    | U => exact hs.elim
    | K => exact hs.elim
    | A => exact hs.elim

/-- A mask with no `true` entry selects nothing. -/
theorem listMask_eq_nil {α : Type*} (m : List Bool) (l : List α)
    (h : ∀ b ∈ m, b = false) : listMask m l = [] := by
  induction m generalizing l with
  | nil => rfl
  | cons b m ih =>
    cases l with
    | nil => rfl
    | cons x l =>
      have hb : b = false := h b List.mem_cons_self
      subst hb
      exact ih l (fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- The mask that is `true` exactly at position `i` selects the `i`-th entry. -/
private theorem listMask_beq_add {α : Type*} : ∀ (l : List α) (j i : ℕ) (hi : i < l.length),
    listMask ((List.range l.length).map fun k => decide (j + k = j + i)) l = [l[i]'hi] := by
  intro l
  induction l with
  | nil => intro j i hi; simp at hi
  | cons x l ih =>
    intro j i hi
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    cases i with
    | zero =>
      have hb : decide (j + 0 = j + 0) = true := by simp
      rw [hb]
      have hrest : listMask (((List.range l.length).map
          ((fun k => decide (j + k = j + 0)) ∘ Nat.succ)) : List Bool) l = [] := by
        refine listMask_eq_nil _ _ fun b hb' => ?_
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb'
        simp
      change x :: listMask _ l = _
      rw [hrest]
      rfl
    | succ i =>
      have hb : decide (j + 0 = j + (i + 1)) = false := by simp
      rw [hb]
      have hmask : ((List.range l.length).map
          ((fun k => decide (j + k = j + (i + 1))) ∘ Nat.succ))
          = (List.range l.length).map (fun k => decide (j + 1 + k = j + 1 + i)) := by
        refine List.map_congr_left fun k _ => ?_
        simp only [Function.comp_apply, decide_eq_decide]
        omega
      change listMask _ l = _
      rw [hmask]
      have hi' : i < l.length := by simpa using hi
      rw [ih (j + 1) i hi']
      rfl

/-- **The single-face mask** selects exactly the `i`-th kernel face. -/
theorem cpmask1 (cp : CProg) (i : ℕ) (h : ConfigProg cp) (hi : i < cpksize cp) :
    cpmask (cfmask1 cp i) cp
      = [(cpker cp)[i]'(by rw [size_cpker h]; exact hi)] := by
  have hlen : (cpker cp).length = cpksize cp := size_cpker h
  simp only [cpmask, cfmask1]
  have h1 : listMask (List.replicate (cprsize cp) false) (cpmap cp).cpring = [] :=
    listMask_eq_nil _ _ fun b hb => List.eq_of_mem_replicate hb
  rw [h1, List.nil_append]
  have h2 : (List.range (cpksize cp)).map (fun j => j == i)
      = (List.range (cpker cp).length).map (fun k => decide (0 + k = 0 + i)) := by
    rw [hlen]
    refine List.map_congr_left fun k _ => ?_
    rw [Bool.eq_iff_iff]
    simp
  rw [h2]
  exact listMask_beq_add (cpker cp) 0 i (by rw [hlen]; exact hi)

/-! ### The faces of a configuration map

The perimeter and the kernel transversal together meet every face exactly
once. -/

/-- The face band only depends on the darts of the list. -/
private theorem fband_perm {D : Type*} {G : Hypermap D} {p q : List D}
    (hpq : p.Perm q) (x : D) : G.Fband p x ↔ G.Fband q x := by
  constructor <;> rintro ⟨y, hy, hxy⟩
  · exact ⟨y, hpq.mem_iff.mp hy, hxy⟩
  · exact ⟨y, hpq.mem_iff.mpr hy, hxy⟩

/-- The kernel transversal of a `Y` step. -/
theorem cpker_Y (cp : CProg) : cpker (.Y :: cp) = (cpker cp).map (injcpStep .Y cp) := rfl

/-- The kernel transversal of an `H` step, at a nontrivial ring. -/
theorem cpker_H_point (cp : CProg) (h : (cpmap cp).Proper) :
    cpker (.H :: cp) = ((cpmap cp).point :: cpker cp).map (injcpStep .H cp) := by
  have hc : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring h
  have h1 : ((cpmap cp).cpring)[1]? = some (cpmap cp).point := by
    rw [hc]
    rfl
  rw [cpker_H, h1]
  rfl

/-- The perimeter of the map of a `Y` step, with its kernel transversal. -/
theorem cpring_append_cpker_Y (cp : CProg) :
    ((cpmap cp).ecpY).cpring ++ (cpker cp).map (cpmap cp).icpY
      = (cpmap cp).ecpY.map.node .X :: .X
        :: (((cpmap cp).cpring.tail ++ cpker cp).map (cpmap cp).icpY) := by
  rw [PointedMap.cpring_ecpY', List.map_append]
  rfl

/-- The perimeter of the map of an `H` step, with its kernel transversal. -/
theorem cpring_append_cpker_H (cp : CProg) (h : (cpmap cp).Proper) :
    ((cpmap cp).ecpH).cpring ++ ((cpmap cp).point :: cpker cp).map (cpmap cp).icpH
      = (cpmap cp).ecpH.map.node .X :: .X
        :: ((((cpmap cp).cpring.drop 2) ++ (cpmap cp).point :: cpker cp).map
              (cpmap cp).icpH) := by
  rw [PointedMap.cpring_ecpH' (cpmap cp) h, List.map_append]
  rfl

/-- The two darts of the initial map lie on different faces. -/
theorem simple_cpmap0 :
    (cpmap []).map.Simple ((cpmap []).cpring ++ cpker []) := by
  have hne : ¬ PointedMap.cpmap0Map.CFace false true := by
    rintro ⟨i, hi⟩
    rw [PointedMap.face_cpmap0Map, one_zpow] at hi
    simp at hi
  have hker : cpker ([] : CProg) = [] := rfl
  have hcp : (cpmap []).cpring ++ cpker [] = [false, true] := by
    rw [hker, List.append_nil]
    exact PointedMap.cpring_cpmap0
  rw [hcp]
  refine Hypermap.simple_cons.mpr ⟨?_, ?_⟩
  · rintro ⟨y, hy, hxy⟩
    have hy' : y = true := List.eq_of_mem_singleton hy
    subst hy'
    exact hne hxy
  · exact List.pairwise_singleton _ _

/-- **The faces of a configuration map are distinct**: the perimeter followed by
the kernel transversal is face-simple. -/
theorem cpmap_simple : ∀ {cp : CProg}, ConfigProg cp →
    (cpmap cp).map.Simple ((cpmap cp).cpring ++ cpker cp) := by
  have key : ∀ (cp : CProg), (cp = [] ∨ ConfigProg cp) →
      (cpmap cp).map.Simple ((cpmap cp).cpring ++ cpker cp) := by
    intro cp
    induction cp with
    | nil => intro _; exact simple_cpmap0
    | cons s cp ih =>
      intro h
      have hcfg : ConfigProg (s :: cp) := by
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hs := hcfg.1 s List.mem_cons_self
      have hsub : cp = [] ∨ ConfigProg cp := by
        by_cases hnil : cp = []
        · exact Or.inl hnil
        · exact Or.inr (hcfg.of_cons hnil)
      have hih := ih hsub
      cases s with
      | R n =>
        have hperm : ((cpmap (.R n :: cp)).cpring ++ cpker (.R n :: cp)).Perm
            ((cpmap cp).cpring ++ cpker cp) := by
          have hring : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
            Hypermap.cpring_ecpR n
          rw [hring]
          exact (List.rotate_perm _ n).append_right _
        exact hih.perm hperm.symm
      | R' => exact hs.elim
      | Y =>
        have hhead : (cpmap cp).cpring
            = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).cpring.tail :=
          Hypermap.head_cpring
        have hih' : (cpmap cp).map.Simple ((cpmap cp).map.node (cpmap cp).point ::
            ((cpmap cp).cpring.tail ++ cpker cp)) := by
          rw [← List.cons_append, ← hhead]
          exact hih
        obtain ⟨hnb, hs'⟩ := Hypermap.simple_cons.mp hih'
        change ((cpmap cp).ecpY).map.Simple
          (((cpmap cp).ecpY).cpring ++ (cpker cp).map (cpmap cp).icpY)
        rw [cpring_append_cpker_Y cp]
        refine Hypermap.simple_cons.mpr ⟨?_, Hypermap.simple_cons.mpr ⟨?_, ?_⟩⟩
        · rintro ⟨y, hy, hxy⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · rcases (PointedMap.cface_ecpY (cpmap cp) _).mp hxy.symm with hc | hc
            · rw [PointedMap.node_ecpY] at hc
              exact absurd hc (by simp)
            · rw [PointedMap.node_ecpY] at hc
              exact absurd (EcpDart.icp_injective hc) (by simp)
          · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
            exact hnb ⟨z, hz, (PointedMap.cface_icpY' (cpmap cp) _ z).mp
              ((PointedMap.cface_node_ecpY' (cpmap cp)).symm.trans hxy)⟩
        · rintro ⟨y, hy, hxy⟩
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
          exact PointedMap.not_cface_ecpY_icpY (cpmap cp) z hxy
        · exact (Hypermap.simple_map (PointedMap.cface_icpY' (cpmap cp)) _).mpr hs'
      | H =>
        have hnil : cp ≠ [] := by
          rintro rfl
          exact absurd hcfg.2 (by simp)
        have hcp := hcfg.of_cons hnil
        have hprop : (cpmap cp).Proper := cpmap_proper hcp.cubicProg
        have hhead : (cpmap cp).cpring
            = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
              :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hprop
        have hih' : (cpmap cp).map.Simple ((cpmap cp).map.node (cpmap cp).point ::
            (cpmap cp).point :: ((cpmap cp).cpring.drop 2 ++ cpker cp)) := by
          rw [← List.cons_append, ← List.cons_append, ← hhead]
          exact hih
        obtain ⟨hnb, hrest⟩ := Hypermap.simple_cons.mp hih'
        have hpm : ((cpmap cp).point :: ((cpmap cp).cpring.drop 2 ++ cpker cp)).Perm
            ((cpmap cp).cpring.drop 2 ++ (cpmap cp).point :: cpker cp) :=
          List.perm_middle.symm
        rw [cpker_H_point cp hprop]
        change ((cpmap cp).ecpH).map.Simple
          (((cpmap cp).ecpH).cpring
            ++ ((cpmap cp).point :: cpker cp).map (cpmap cp).icpH)
        rw [cpring_append_cpker_H cp hprop]
        refine Hypermap.simple_cons.mpr ⟨?_, Hypermap.simple_cons.mpr ⟨?_, ?_⟩⟩
        · rintro ⟨y, hy, hxy⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · rcases (PointedMap.cface_ecpH (cpmap cp) hprop _).mp hxy.symm with hc | hc | hc
            · rw [PointedMap.node_ecpH _ hprop] at hc
              exact absurd hc (by simp)
            · rw [PointedMap.node_ecpH _ hprop] at hc
              exact absurd (EcpDart.icp_injective hc) (by simp)
            · rw [PointedMap.node_ecpH _ hprop] at hc
              exact absurd (EcpDart.icp_injective (EcpDart.icp_injective hc)) (by simp)
          · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
            refine hnb ((fband_perm hpm _).mpr ⟨z, hz, ?_⟩)
            exact (PointedMap.cface_icpH' (cpmap cp) _ z).mp
              ((PointedMap.cface_node_ecpH' (cpmap cp) hprop).symm.trans hxy)
        · rintro ⟨y, hy, hxy⟩
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
          exact PointedMap.not_cface_ecpH_icpH (cpmap cp) hprop z hxy
        · refine (Hypermap.simple_map (PointedMap.cface_icpH' (cpmap cp)) _).mpr ?_
          exact hrest.perm hpm
      | U => exact hs.elim
      | K => exact hs.elim
      | A => exact hs.elim
  exact fun {cp} hcp => key cp (Or.inr hcp)

/-- **The faces of a configuration map are covered**: every dart lies on the
face of a perimeter dart or of a kernel dart. -/
theorem cpmap_cover : ∀ {cp : CProg}, ConfigProg cp → ∀ u : (cpmap cp).Dart,
    (cpmap cp).map.Fband ((cpmap cp).cpring ++ cpker cp) u := by
  have key : ∀ (cp : CProg), (cp = [] ∨ ConfigProg cp) → ∀ u : (cpmap cp).Dart,
      (cpmap cp).map.Fband ((cpmap cp).cpring ++ cpker cp) u := by
    intro cp
    induction cp with
    | nil =>
      intro _ u
      have hker : cpker ([] : CProg) = [] := rfl
      have hcp : (cpmap []).cpring ++ cpker [] = [false, true] := by
        rw [hker, List.append_nil]
        exact PointedMap.cpring_cpmap0
      rw [hcp]
      refine Hypermap.fband_of_mem ?_
      cases u with
      | false => exact List.mem_cons_self
      | true => exact List.mem_cons_of_mem _ List.mem_cons_self
    | cons s cp ih =>
      intro h u
      have hcfg : ConfigProg (s :: cp) := by
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hs := hcfg.1 s List.mem_cons_self
      have hsub : cp = [] ∨ ConfigProg cp := by
        by_cases hnil : cp = []
        · exact Or.inl hnil
        · exact Or.inr (hcfg.of_cons hnil)
      have hih := ih hsub
      cases s with
      | R n =>
        have hperm : ((cpmap (.R n :: cp)).cpring ++ cpker (.R n :: cp)).Perm
            ((cpmap cp).cpring ++ cpker cp) := by
          have hring : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
            Hypermap.cpring_ecpR n
          rw [hring]
          exact (List.rotate_perm _ n).append_right _
        exact (fband_perm hperm u).mpr (hih u)
      | R' => exact hs.elim
      | Y =>
        have hhead : (cpmap cp).cpring
            = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).cpring.tail :=
          Hypermap.head_cpring
        change ((cpmap cp).ecpY).map.Fband
          (((cpmap cp).ecpY).cpring ++ (cpker cp).map (cpmap cp).icpY) u
        rw [cpring_append_cpker_Y cp]
        rcases PointedMap.fband_icpY' (cpmap cp) u with ⟨x, hx⟩ | hX
        · obtain ⟨z, hz, hxz⟩ := hih x
          rw [hhead] at hz
          have hface : (cpmap cp).ecpY.map.CFace u ((cpmap cp).icpY z) :=
            hx.trans ((PointedMap.cface_icpY' (cpmap cp) _ _).mpr hxz)
          rcases List.mem_cons.mp hz with rfl | hz
          · exact Hypermap.fband_cons.mpr (Or.inl
              (hface.trans (PointedMap.cface_node_ecpY' (cpmap cp)).symm))
          · refine Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inr ?_)))
            exact ⟨(cpmap cp).icpY z, List.mem_map.mpr ⟨z, hz, rfl⟩, hface⟩
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inl hX.symm)))
      | H =>
        have hnil : cp ≠ [] := by
          rintro rfl
          exact absurd hcfg.2 (by simp)
        have hcp := hcfg.of_cons hnil
        have hprop : (cpmap cp).Proper := cpmap_proper hcp.cubicProg
        have hhead : (cpmap cp).cpring
            = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
              :: (cpmap cp).cpring.drop 2 := Hypermap.head_proper_cpring hprop
        rw [cpker_H_point cp hprop]
        change ((cpmap cp).ecpH).map.Fband
          (((cpmap cp).ecpH).cpring
            ++ ((cpmap cp).point :: cpker cp).map (cpmap cp).icpH) u
        rw [cpring_append_cpker_H cp hprop]
        rcases PointedMap.fband_icpH' (cpmap cp) u with ⟨x, hx⟩ | hX
        · obtain ⟨z, hz, hxz⟩ := hih x
          rw [hhead] at hz
          have hface : (cpmap cp).ecpH.map.CFace u ((cpmap cp).icpH z) :=
            hx.trans ((PointedMap.cface_icpH' (cpmap cp) _ _).mpr hxz)
          rcases List.mem_cons.mp hz with rfl | hz1
          · exact Hypermap.fband_cons.mpr (Or.inl
              (hface.trans (PointedMap.cface_node_ecpH' (cpmap cp) hprop).symm))
          refine Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inr ?_)))
          rcases List.mem_cons.mp hz1 with rfl | hz2
          · exact ⟨(cpmap cp).icpH (cpmap cp).point, List.mem_map.mpr
              ⟨(cpmap cp).point, List.mem_append_right _ List.mem_cons_self, rfl⟩, hface⟩
          · rcases List.mem_append.mp hz2 with hz3 | hz3
            · exact ⟨(cpmap cp).icpH z, List.mem_map.mpr
                ⟨z, List.mem_append_left _ hz3, rfl⟩, hface⟩
            · exact ⟨(cpmap cp).icpH z, List.mem_map.mpr
                ⟨z, List.mem_append_right _ (List.mem_cons_of_mem _ hz3), rfl⟩, hface⟩
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inl hX.symm)))
      | U => exact hs.elim
      | K => exact hs.elim
      | A => exact hs.elim
  exact fun {cp} hcp => key cp (Or.inr hcp)

/-- The single-face masks are proper. -/
theorem properCfMask1 (cp : CProg) (i : ℕ) : (cfmask1 cp i).Proper cp := by
  constructor <;> simp [cfmask1]

/-! ### Selecting darts with a mask

`AnyMask Q m l` says that some dart of `l` selected by the mask `m` satisfies
`Q`; both sides of the adjacency-mask correctness statement are of this
shape. -/

/-- A mask of `false`s selects nothing, and so does an empty mask. -/
theorem listMask_nil_mask {α : Type*} (l : List α) : listMask [] l = [] := by
  cases l <;> rfl

/-- Nothing is selected from the empty list. -/
theorem listMask_nil_list {α : Type*} (m : List Bool) :
    listMask m ([] : List α) = ([] : List α) := by
  cases m <;> rfl

/-- Every selected dart is a dart of the list. -/
theorem mem_of_mem_listMask {α : Type*} : ∀ (m : List Bool) (l : List α) {y : α},
    y ∈ listMask m l → y ∈ l := by
  intro m
  induction m with
  | nil => intro l y hy; rw [listMask_nil_mask] at hy; exact absurd hy (by simp)
  | cons b m ih =>
    intro l y hy
    cases l with
    | nil => rw [listMask_nil_list] at hy; exact absurd hy (by simp)
    | cons x l =>
      cases b with
      | false => exact List.mem_cons_of_mem _ (ih l hy)
      | true =>
        have hy' : y ∈ x :: listMask m l := hy
        rcases List.mem_cons.mp hy' with rfl | hy'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih l hy')

/-- Selecting commutes with mapping. -/
theorem listMask_map {α β : Type*} (f : α → β) (m : List Bool) : ∀ l : List α,
    listMask m (l.map f) = (listMask m l).map f := by
  induction m with
  | nil => intro l; rw [listMask_nil_mask, listMask_nil_mask, List.map_nil]
  | cons b m ih =>
    intro l
    cases l with
    | nil => rw [List.map_nil, listMask_nil_list, listMask_nil_list, List.map_nil]
    | cons x l =>
      cases b with
      | false => exact ih l
      | true =>
        have h1 : listMask (true :: m) ((x :: l).map f) = f x :: listMask m (l.map f) := rfl
        have h2 : listMask (true :: m) (x :: l) = x :: listMask m l := rfl
        rw [h1, h2, ih l, List.map_cons]

/-- Selecting from a concatenation, when the first mask has the right length. -/
theorem listMask_append {α : Type*} : ∀ (m₁ : List Bool) (l₁ : List α),
    m₁.length = l₁.length → ∀ (m₂ : List Bool) (l₂ : List α),
      listMask (m₁ ++ m₂) (l₁ ++ l₂) = listMask m₁ l₁ ++ listMask m₂ l₂ := by
  intro m₁
  induction m₁ with
  | nil =>
    intro l₁ hlen m₂ l₂
    have : l₁ = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst this
    rw [listMask_nil_mask, List.nil_append, List.nil_append, List.nil_append]
  | cons b m₁ ih =>
    intro l₁ hlen m₂ l₂
    cases l₁ with
    | nil => simp at hlen
    | cons x l₁ =>
      have hlen' : m₁.length = l₁.length := by simpa using hlen
      cases b with
      | false =>
        have h1 : listMask (false :: (m₁ ++ m₂)) (x :: (l₁ ++ l₂))
            = listMask (m₁ ++ m₂) (l₁ ++ l₂) := rfl
        have h2 : listMask (false :: m₁) (x :: l₁) = listMask m₁ l₁ := rfl
        rw [List.cons_append, List.cons_append, h1, h2, ih l₁ hlen' m₂ l₂]
      | true =>
        have h1 : listMask (true :: (m₁ ++ m₂)) (x :: (l₁ ++ l₂))
            = x :: listMask (m₁ ++ m₂) (l₁ ++ l₂) := rfl
        have h2 : listMask (true :: m₁) (x :: l₁) = x :: listMask m₁ l₁ := rfl
        rw [List.cons_append, List.cons_append, h1, h2, ih l₁ hlen' m₂ l₂,
          List.cons_append]

/-- Some dart selected by a mask satisfies a predicate. -/
def AnyMask {α : Type*} (Q : α → Prop) (m : List Bool) (l : List α) : Prop :=
  ∃ y ∈ listMask m l, Q y

/-- Nothing is selected by the empty mask. -/
theorem anyMask_nil_mask {α : Type*} (Q : α → Prop) (l : List α) : ¬ AnyMask Q [] l := by
  rintro ⟨y, hy, -⟩
  rw [listMask_nil_mask] at hy
  exact absurd hy (by simp)

/-- Nothing is selected from the empty list. -/
theorem anyMask_nil_list {α : Type*} (Q : α → Prop) (m : List Bool) : ¬ AnyMask Q m [] := by
  rintro ⟨y, hy, -⟩
  rw [listMask_nil_list] at hy
  exact absurd hy (by simp)

/-- Peeling the first entry off a mask. -/
theorem anyMask_cons {α : Type*} (Q : α → Prop) (b : Bool) (m : List Bool) (x : α)
    (l : List α) : AnyMask Q (b :: m) (x :: l) ↔ (b = true ∧ Q x) ∨ AnyMask Q m l := by
  cases b with
  | false =>
    have h : AnyMask Q (false :: m) (x :: l) ↔ AnyMask Q m l := Iff.rfl
    rw [h]
    simp
  | true =>
    have h : listMask (true :: m) (x :: l) = x :: listMask m l := rfl
    constructor
    · rintro ⟨y, hy, hQ⟩
      rw [h] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Or.inl ⟨rfl, hQ⟩
      · exact Or.inr ⟨y, hy, hQ⟩
    · rintro (⟨-, hQ⟩ | ⟨y, hy, hQ⟩)
      · exact ⟨x, by rw [h]; exact List.mem_cons_self, hQ⟩
      · exact ⟨y, by rw [h]; exact List.mem_cons_of_mem _ hy, hQ⟩

/-- Selecting from a mapped list. -/
theorem anyMask_map {α β : Type*} (Q : β → Prop) (f : α → β) (m : List Bool) (l : List α) :
    AnyMask Q m (l.map f) ↔ AnyMask (fun x => Q (f x)) m l := by
  unfold AnyMask
  rw [listMask_map]
  constructor
  · rintro ⟨y, hy, hQ⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact ⟨x, hx, hQ⟩
  · rintro ⟨x, hx, hQ⟩
    exact ⟨f x, List.mem_map.mpr ⟨x, hx, rfl⟩, hQ⟩

/-- Replacing the predicate by an equivalent one. -/
theorem anyMask_congr {α : Type*} {Q Q' : α → Prop} (h : ∀ y, Q y ↔ Q' y) (m : List Bool)
    (l : List α) : AnyMask Q m l ↔ AnyMask Q' m l := by
  constructor <;> rintro ⟨y, hy, hQ⟩
  · exact ⟨y, hy, (h y).mp hQ⟩
  · exact ⟨y, hy, (h y).mpr hQ⟩

/-- Nothing is selected when the predicate fails on every dart of the list. -/
theorem anyMask_eq_false {α : Type*} {Q : α → Prop} {m : List Bool} {l : List α}
    (h : ∀ y ∈ l, ¬ Q y) : ¬ AnyMask Q m l := by
  rintro ⟨y, hy, hQ⟩
  exact h y (mem_of_mem_listMask m l hy) hQ

/-- Some dart of a permuted list satisfies a predicate exactly when some dart of
the original does. -/
private theorem exists_mem_perm {α : Type*} {Q : α → Prop} {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : (∃ y ∈ l₁, Q y) ↔ (∃ y ∈ l₂, Q y) := by
  constructor <;> rintro ⟨y, hy, hQ⟩
  · exact ⟨y, h.mem_iff.mp hy, hQ⟩
  · exact ⟨y, h.mem_iff.mpr hy, hQ⟩

/-! ### The adjacency mask

`cpadj cm cp` is the mask of the faces of `cpmap cp` that are adjacent to a face
selected by `cm`.  It is computed by the same recursion as `cpmap`, reading off
from each construction step which faces it makes adjacent. -/

/-- Rotating a mask backwards by `n`: the inverse of `List.rotate n`. -/
def rotrMask (n : ℕ) (m : List Bool) : List Bool := m.rotate (m.length - n % m.length)

/-- `rotrMask` is a left inverse of rotation. -/
theorem rotate_rotrMask (n : ℕ) (m : List Bool) : (rotrMask n m).rotate n = m := by
  rcases Nat.eq_zero_or_pos m.length with hL | hL
  · rw [List.length_eq_zero_iff] at hL
    subst hL
    simp [rotrMask]
  · rw [rotrMask, List.rotate_rotate]
    have hd : m.length * (n / m.length) + n % m.length = n := Nat.div_add_mod n m.length
    have hmod : n % m.length < m.length := Nat.mod_lt _ hL
    have hkey : m.length - n % m.length + n = m.length * (1 + n / m.length) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hkey]
    exact rotate_length_mul m _

/-- `rotrMask` does not change the length. -/
@[simp] theorem length_rotrMask (n : ℕ) (m : List Bool) :
    (rotrMask n m).length = m.length := by
  rw [rotrMask, List.length_rotate]

/-- Adjusting the first entry of the remaining ring mask in an `H` step. -/
def cpadjTail (b : Bool) : List Bool → List Bool
  | [] => []
  | a :: m => (a || b) :: m

/-- `cpadjTail` does not change the length. -/
@[simp] theorem length_cpadjTail (b : Bool) (m : List Bool) :
    (cpadjTail b m).length = m.length := by
  cases m <;> rfl

/-- The mask of the faces adjacent to the faces selected by `cm`. -/
def cpadj : CfMask → CProg → CfMask
  | cm, [] =>
      match cm.ring with
      | [b0, b1] => ⟨[b1, b0], []⟩
      | _ => cm
  | cm, .R n :: cp =>
      ⟨(cpadj ⟨rotrMask n cm.ring, cm.kernel⟩ cp).ring.rotate n,
       (cpadj ⟨rotrMask n cm.ring, cm.kernel⟩ cp).kernel⟩
  | cm, .Y :: cp =>
      match cm.ring with
      | b0 :: b1 :: b2 :: mr =>
          match cpadj ⟨b0 :: b2 :: mr, cm.kernel⟩ cp with
          | ⟨a0 :: a2 :: mr', mk'⟩ => ⟨(a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr', mk'⟩
          | _ => cm
      | _ => cm
  | cm, .H :: cp =>
      match cm.ring with
      | b0 :: b1 :: mr =>
          match cm.kernel with
          | b1' :: km =>
              match cpadj ⟨b0 :: b1' :: mr, km⟩ cp with
              | ⟨a0 :: a1 :: mr', mk'⟩ =>
                  ⟨(a0 || b1) :: ((b0 || b1') || mr.headD b0) :: cpadjTail b1 mr',
                   (a1 || b1) :: mk'⟩
              | _ => cm
          | _ => cm
      | _ => cm
  | cm, _ :: _ => cm

/-- Unfolding `cpadj` on the empty program. -/
theorem cpadj_nil (b0 b1 : Bool) (km : List Bool) :
    cpadj ⟨[b0, b1], km⟩ [] = ⟨[b1, b0], []⟩ := rfl

/-- Unfolding `cpadj` on an `R` step. -/
theorem cpadj_R (n : ℕ) (cp : CProg) (mr km : List Bool) :
    cpadj ⟨mr, km⟩ (.R n :: cp)
      = ⟨(cpadj ⟨rotrMask n mr, km⟩ cp).ring.rotate n,
         (cpadj ⟨rotrMask n mr, km⟩ cp).kernel⟩ := rfl

/-- Unfolding `cpadj` on a `Y` step. -/
theorem cpadj_Y (cp : CProg) (b0 b1 b2 : Bool) (mr km : List Bool) :
    cpadj ⟨b0 :: b1 :: b2 :: mr, km⟩ (.Y :: cp)
      = (match cpadj ⟨b0 :: b2 :: mr, km⟩ cp with
         | ⟨a0 :: a2 :: mr', mk'⟩ => ⟨(a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr', mk'⟩
         | _ => ⟨b0 :: b1 :: b2 :: mr, km⟩) := rfl

/-- Unfolding `cpadj` on a `Y` step whose recursive value is long enough. -/
theorem cpadj_Y_of (cp : CProg) (b0 b1 b2 : Bool) (mr km : List Bool)
    (a0 a2 : Bool) (mr' mk' : List Bool)
    (h : cpadj ⟨b0 :: b2 :: mr, km⟩ cp = ⟨a0 :: a2 :: mr', mk'⟩) :
    cpadj ⟨b0 :: b1 :: b2 :: mr, km⟩ (.Y :: cp)
      = ⟨(a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr', mk'⟩ := by
  rw [cpadj_Y, h]

/-- Unfolding `cpadj` on an `H` step. -/
theorem cpadj_H (cp : CProg) (b0 b1 b1' : Bool) (mr km : List Bool) :
    cpadj ⟨b0 :: b1 :: mr, b1' :: km⟩ (.H :: cp)
      = (match cpadj ⟨b0 :: b1' :: mr, km⟩ cp with
         | ⟨a0 :: a1 :: mr', mk'⟩ =>
             ⟨(a0 || b1) :: ((b0 || b1') || mr.headD b0) :: cpadjTail b1 mr',
              (a1 || b1) :: mk'⟩
         | _ => ⟨b0 :: b1 :: mr, b1' :: km⟩) := rfl

/-- Unfolding `cpadj` on an `H` step whose recursive value is long enough. -/
theorem cpadj_H_of (cp : CProg) (b0 b1 b1' : Bool) (mr km : List Bool)
    (a0 a1 : Bool) (mr' mk' : List Bool)
    (h : cpadj ⟨b0 :: b1' :: mr, km⟩ cp = ⟨a0 :: a1 :: mr', mk'⟩) :
    cpadj ⟨b0 :: b1 :: mr, b1' :: km⟩ (.H :: cp)
      = ⟨(a0 || b1) :: ((b0 || b1') || mr.headD b0) :: cpadjTail b1 mr',
         (a1 || b1) :: mk'⟩ := by
  rw [cpadj_H, h]

/-- **The adjacency mask is proper**: it has the same shape as its argument. -/
theorem cpadj_proper : ∀ (cp : CProg) (cm : CfMask),
    cm.Proper cp → (cpadj cm cp).Proper cp := by
  intro cp
  induction cp with
  | nil =>
    rintro ⟨mr, km⟩ ⟨h1, h2⟩
    have h1' : mr.length = 2 := h1
    rcases mr with _ | ⟨b0, mr⟩
    · simp at h1'
    rcases mr with _ | ⟨b1, mr⟩
    · simp at h1'
    rcases mr with _ | ⟨b2, mr⟩
    · rw [cpadj_nil]
      exact ⟨rfl, rfl⟩
    · simp at h1'
  | cons s cp ih =>
    rintro ⟨mr, km⟩ ⟨h1, h2⟩
    cases s with
    | R n =>
      have h1' : (rotrMask n mr).length = cprsize cp := by
        rw [length_rotrMask]
        exact h1
      have hrec := ih ⟨rotrMask n mr, km⟩ ⟨h1', h2⟩
      rw [cpadj_R]
      exact ⟨by rw [List.length_rotate]; exact hrec.1, hrec.2⟩
    | R' => exact ⟨h1, h2⟩
    | Y =>
      have hcpr : cprsize (.Y :: cp) = cprsize cp + 1 := rfl
      have hcpk : cpksize (.Y :: cp) = cpksize cp := rfl
      have h1' : mr.length = cprsize cp + 1 := by rw [← hcpr]; exact h1
      have h2' : km.length = cpksize cp := by rw [← hcpk]; exact h2
      rcases mr with _ | ⟨b0, mr⟩
      · exact ⟨h1, h2⟩
      rcases mr with _ | ⟨b1, mr⟩
      · exact ⟨h1, h2⟩
      rcases mr with _ | ⟨b2, mr⟩
      · exact ⟨h1, h2⟩
      obtain ⟨mr2, mk2, hres⟩ : ∃ mr2 mk2, cpadj ⟨b0 :: b2 :: mr, km⟩ cp = ⟨mr2, mk2⟩ :=
        ⟨_, _, rfl⟩
      have hprop : (⟨b0 :: b2 :: mr, km⟩ : CfMask).Proper cp := by
        refine ⟨?_, h2'⟩
        simp only [List.length_cons] at h1' ⊢
        omega
      have hrec := ih _ hprop
      rw [hres] at hrec
      rw [cpadj_Y, hres]
      rcases mr2 with _ | ⟨a0, mr2⟩
      · exact ⟨h1, h2⟩
      rcases mr2 with _ | ⟨a2, mr2⟩
      · exact ⟨h1, h2⟩
      have hr1 := hrec.1
      have hr2 := hrec.2
      refine ⟨?_, ?_⟩
      · rw [hcpr]
        simp only [List.length_cons] at hr1 ⊢
        omega
      · rw [hcpk]
        exact hr2
    | H =>
      have hcpr : cprsize (.H :: cp) = cprsize cp := rfl
      have hcpk : cpksize (.H :: cp) = cpksize cp + 1 := rfl
      have h1' : mr.length = cprsize cp := by rw [← hcpr]; exact h1
      have h2' : km.length = cpksize cp + 1 := by rw [← hcpk]; exact h2
      rcases mr with _ | ⟨b0, mr⟩
      · exact ⟨h1, h2⟩
      rcases mr with _ | ⟨b1, mr⟩
      · exact ⟨h1, h2⟩
      rcases km with _ | ⟨b1', km⟩
      · exact ⟨h1, h2⟩
      obtain ⟨mr2, mk2, hres⟩ : ∃ mr2 mk2, cpadj ⟨b0 :: b1' :: mr, km⟩ cp = ⟨mr2, mk2⟩ :=
        ⟨_, _, rfl⟩
      have hprop : (⟨b0 :: b1' :: mr, km⟩ : CfMask).Proper cp := by
        refine ⟨h1', ?_⟩
        simp only [List.length_cons] at h2' ⊢
        omega
      have hrec := ih _ hprop
      rw [hres] at hrec
      rw [cpadj_H, hres]
      rcases mr2 with _ | ⟨a0, mr2⟩
      · exact ⟨h1, h2⟩
      rcases mr2 with _ | ⟨a1, mr2⟩
      · exact ⟨h1, h2⟩
      have hr1 := hrec.1
      have hr2 := hrec.2
      refine ⟨?_, ?_⟩
      · rw [hcpr]
        simp only [List.length_cons, length_cpadjTail] at hr1 ⊢
        omega
      · rw [hcpk]
        simp only [List.length_cons] at hr2 ⊢
        omega
    | U => exact ⟨h1, h2⟩
    | K => exact ⟨h1, h2⟩
    | A => exact ⟨h1, h2⟩

/-! ### Correctness of the adjacency mask -/

/-- The perimeter and kernel of a configuration map, or of the initial map, are
face-simple. -/
private theorem cpmap_simple' (cp : CProg) (h : cp = [] ∨ ConfigProg cp) :
    (cpmap cp).map.Simple ((cpmap cp).cpring ++ cpker cp) := by
  rcases h with rfl | h
  · exact simple_cpmap0
  · exact cpmap_simple h

/-- The map of a configuration program, or the initial map, has a nontrivial
ring. -/
private theorem cpmap_proper' (cp : CProg) (h : cp = [] ∨ ConfigProg cp) :
    (cpmap cp).Proper := by
  rcases h with rfl | h
  · exact PointedMap.proper_cpmap0
  · exact cpmap_proper h.cubicProg

/-- The map of a configuration program, or the initial map, is plain. -/
private theorem cpmap_plain' (cp : CProg) (h : cp = [] ∨ ConfigProg cp) :
    (cpmap cp).Plain := by
  rcases h with rfl | h
  · exact cpmap_plain cubicProg_nil
  · exact cpmap_plain h.cubicProg

/-- The darts selected by a mask split into ring and kernel. -/
theorem exists_mem_cpmask {cp : CProg} {cm : CfMask} {Q : (cpmap cp).Dart → Prop} :
    (∃ y ∈ cpmask cm cp, Q y)
      ↔ AnyMask Q cm.ring (cpmap cp).cpring ∨ AnyMask Q cm.kernel (cpker cp) := by
  constructor
  · rintro ⟨y, hy, hQ⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact Or.inl ⟨y, hy, hQ⟩
    · exact Or.inr ⟨y, hy, hQ⟩
  · rintro (⟨y, hy, hQ⟩ | ⟨y, hy, hQ⟩)
    · exact ⟨y, List.mem_append_left _ hy, hQ⟩
    · exact ⟨y, List.mem_append_right _ hy, hQ⟩

/-- The face band of a masked set of darts. -/
theorem fband_cpmask {cp : CProg} {cm : CfMask} (u : (cpmap cp).Dart) :
    (cpmap cp).map.Fband (cpmask cm cp) u
      ↔ AnyMask (fun y => (cpmap cp).map.CFace u y) cm.ring (cpmap cp).cpring
        ∨ AnyMask (fun y => (cpmap cp).map.CFace u y) cm.kernel (cpker cp) :=
  exists_mem_cpmask

/-- Rotating a mask and the list it selects from permutes what it selects. -/
theorem listMask_rotate_perm {α : Type*} (m : List Bool) (l : List α)
    (hlen : m.length = l.length) (n : ℕ) :
    (listMask (m.rotate n) (l.rotate n)).Perm (listMask m l) := by
  rcases Nat.eq_zero_or_pos l.length with hL | hL
  · have hl : l = [] := List.eq_nil_of_length_eq_zero hL
    have hm : m = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hL])
    subst hl
    subst hm
    simp only [List.rotate_nil]
    exact List.Perm.refl _
  · have hkle : n % l.length ≤ l.length := le_of_lt (Nat.mod_lt _ hL)
    have hkle' : n % l.length ≤ m.length := by rw [hlen]; exact hkle
    have hmrot : m.rotate n = m.drop (n % l.length) ++ m.take (n % l.length) := by
      rw [← List.rotate_mod m n, hlen, List.rotate_eq_drop_append_take hkle']
    have hlrot : l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) := by
      rw [← List.rotate_mod l n, List.rotate_eq_drop_append_take hkle]
    have hlen1 : (m.drop (n % l.length)).length = (l.drop (n % l.length)).length := by
      rw [List.length_drop, List.length_drop, hlen]
    have hlen2 : (m.take (n % l.length)).length = (l.take (n % l.length)).length := by
      rw [List.length_take, List.length_take, hlen]
    have hmask : listMask (m.rotate n) (l.rotate n)
        = listMask (m.drop (n % l.length)) (l.drop (n % l.length))
          ++ listMask (m.take (n % l.length)) (l.take (n % l.length)) := by
      rw [hmrot, hlrot, listMask_append _ _ hlen1]
    have hmask2 : listMask (m.take (n % l.length)) (l.take (n % l.length))
        ++ listMask (m.drop (n % l.length)) (l.drop (n % l.length)) = listMask m l := by
      rw [← listMask_append _ _ hlen2, List.take_append_drop, List.take_append_drop]
    rw [hmask, ← hmask2]
    exact List.perm_append_comm

/-- Rotating a mask and the list it selects from does not change what it
selects. -/
theorem anyMask_rotate {α : Type*} (Q : α → Prop) (m : List Bool) (l : List α)
    (hlen : m.length = l.length) (n : ℕ) :
    AnyMask Q (m.rotate n) (l.rotate n) ↔ AnyMask Q m l :=
  exists_mem_perm (listMask_rotate_perm m l hlen n)

/-- Rotating the ring mask of an `R` step permutes the darts it selects. -/
private theorem cpmask_rotate_perm (n : ℕ) (cp : CProg) (mrA km : List Bool)
    (hlen : mrA.length = (cpmap cp).cpring.length) :
    (cpmask (⟨mrA.rotate n, km⟩ : CfMask) (.R n :: cp)).Perm
      (cpmask (⟨mrA, km⟩ : CfMask) cp) := by
  have hring : (cpmap (.R n :: cp)).cpring = (cpmap cp).cpring.rotate n :=
    Hypermap.cpring_ecpR n
  have h0 : cpmask (⟨mrA.rotate n, km⟩ : CfMask) (.R n :: cp)
      = listMask (mrA.rotate n) ((cpmap (.R n :: cp)).cpring)
        ++ listMask km (cpker (.R n :: cp)) := rfl
  rw [h0, hring]
  exact List.Perm.append_right _ (listMask_rotate_perm mrA (cpmap cp).cpring hlen n)

/-- Nothing is selected by the empty mask. -/
@[simp] theorem anyMask_nil_mask_iff {α : Type*} (Q : α → Prop) (l : List α) :
    AnyMask Q [] l ↔ False := iff_false_intro (anyMask_nil_mask Q l)

/-- Nothing is selected from the empty list. -/
@[simp] theorem anyMask_nil_list_iff {α : Type*} (Q : α → Prop) (m : List Bool) :
    AnyMask Q m ([] : List α) ↔ False := iff_false_intro (anyMask_nil_list Q m)

/-- Nothing satisfies the always-false predicate. -/
@[simp] theorem anyMask_false {α : Type*} (m : List Bool) (l : List α) :
    AnyMask (fun _ : α => False) m l ↔ False :=
  iff_false_intro (fun h => h.elim fun _ h' => h'.2)

/-- Peeling two entries off a mask. -/
theorem anyMask_cons2 {α : Type*} (Q : α → Prop) (c0 c1 : Bool) (m : List Bool)
    (x0 x1 : α) (l : List α) :
    AnyMask Q (c0 :: c1 :: m) (x0 :: x1 :: l)
      ↔ (c0 = true ∧ Q x0) ∨ (c1 = true ∧ Q x1) ∨ AnyMask Q m l := by
  rw [anyMask_cons, anyMask_cons]

/-- Peeling three entries off a mask. -/
theorem anyMask_cons3 {α : Type*} (Q : α → Prop) (c0 c1 c2 : Bool) (m : List Bool)
    (x0 x1 x2 : α) (l : List α) :
    AnyMask Q (c0 :: c1 :: c2 :: m) (x0 :: x1 :: x2 :: l)
      ↔ (c0 = true ∧ Q x0) ∨ (c1 = true ∧ Q x1) ∨ (c2 = true ∧ Q x2) ∨ AnyMask Q m l := by
  rw [anyMask_cons, anyMask_cons, anyMask_cons]

/-- Peeling the first entry off a mask over a mapped list. -/
theorem anyMask_map_cons {α β : Type*} (Q : β → Prop) (c : Bool) (m : List Bool)
    (z : α) (l : List α) (f : α → β) :
    AnyMask Q (c :: m) ((z :: l).map f)
      ↔ (c = true ∧ Q (f z)) ∨ AnyMask (fun w => Q (f w)) m l := by
  rw [List.map_cons, anyMask_cons, anyMask_map]

/-- Decomposing the ring mask of a `Y` or `H` step. -/
theorem anyMask_ring {α β : Type*} (Q : β → Prop) (c0 c1 c2 : Bool) (m : List Bool)
    (n0 n1 : β) (z : α) (l : List α) (f : α → β) :
    AnyMask Q (c0 :: c1 :: c2 :: m) (n0 :: n1 :: ((z :: l).map f))
      ↔ (c0 = true ∧ Q n0) ∨ (c1 = true ∧ Q n1) ∨ (c2 = true ∧ Q (f z))
        ∨ AnyMask (fun w => Q (f w)) m l := by
  rw [anyMask_cons, anyMask_cons, List.map_cons, anyMask_cons, anyMask_map]

/-! #### The initial map -/

/-- The faces of the initial map are its two darts. -/
theorem cface_cpmap0 (x y : (cpmap []).Dart) : (cpmap []).map.CFace x y ↔ x = y := by
  constructor
  · rintro ⟨i, hi⟩
    have hi' : ((PointedMap.cpmap0Map.face) ^ i) x = y := hi
    rw [PointedMap.face_cpmap0Map, one_zpow] at hi'
    have hx : (1 : Equiv.Perm Bool) x = x := rfl
    rw [hx] at hi'
    exact hi'
  · rintro rfl
    exact Equiv.Perm.SameCycle.refl _ _

/-- The two faces of the initial map are adjacent. -/
theorem adj_cpmap0 (x y : (cpmap []).Dart) : (cpmap []).map.Adj x y ↔ y = !x := by
  have he : ∀ b : (cpmap []).Dart, (cpmap []).map.edge b = !b := fun _ => rfl
  constructor
  · rintro ⟨z, hz, hrz⟩
    have hzx : x = z := (cface_cpmap0 x z).mp hz
    subst hzx
    have hrz' : (cpmap []).map.CFace ((cpmap []).map.edge x) y := hrz
    rw [he] at hrz'
    exact ((cface_cpmap0 _ y).mp hrz').symm
  · rintro rfl
    refine ⟨x, Equiv.Perm.SameCycle.refl _ _, ?_⟩
    have : (cpmap []).map.CFace ((cpmap []).map.edge x) (!x) := by
      rw [he]
      exact Equiv.Perm.SameCycle.refl _ _
    exact this

/-! #### Adapters for the `Y` step -/

private theorem cface_injY (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (.Y :: cp)).map.CFace (injcpStep .Y cp x) (injcpStep .Y cp y)
      ↔ (cpmap cp).map.CFace x y := PointedMap.cface_icpY' (cpmap cp) x y

private theorem adj_injY (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (.Y :: cp)).map.Adj (injcpStep .Y cp x) (injcpStep .Y cp y)
      ↔ (cpmap cp).map.Adj x y := PointedMap.adj_icpY' (cpmap cp) x y

private theorem fband_injY (cp : CProg) (u : (cpmap (.Y :: cp)).Dart) :
    (∃ x : (cpmap cp).Dart, (cpmap (.Y :: cp)).map.CFace u (injcpStep .Y cp x))
      ∨ (cpmap (.Y :: cp)).map.CFace .X u := PointedMap.fband_icpY' (cpmap cp) u

private theorem not_cface_X_injY (cp : CProg) (x : (cpmap cp).Dart) :
    ¬ (cpmap (.Y :: cp)).map.CFace (.X : (cpmap (.Y :: cp)).Dart) (injcpStep .Y cp x) :=
  PointedMap.not_cface_ecpY_icpY (cpmap cp) x

private theorem cface_node_injY (cp : CProg) :
    (cpmap (.Y :: cp)).map.CFace ((cpmap (.Y :: cp)).map.node .X)
      (injcpStep .Y cp ((cpmap cp).map.node (cpmap cp).point)) :=
  PointedMap.cface_node_ecpY' (cpmap cp)

private theorem adj_X_ecpY (cp : CProg) (h : (cpmap cp).Proper)
    (u : (cpmap (.Y :: cp)).Dart) :
    (cpmap (.Y :: cp)).map.Adj .X u
      ↔ (cpmap (.Y :: cp)).map.CFace u
            (injcpStep .Y cp ((cpmap cp).map.node (cpmap cp).point))
        ∨ (cpmap (.Y :: cp)).map.CFace u (injcpStep .Y cp (cpmap cp).point) :=
  PointedMap.adj_ecpY (cpmap cp) h u

private theorem cface_X_ecpY (cp : CProg) (u : (cpmap (.Y :: cp)).Dart) :
    (cpmap (.Y :: cp)).map.CFace .X u ↔ u = .X ∨ u = .icp .X :=
  PointedMap.cface_ecpY (cpmap cp) u

private theorem node_X_ecpY (cp : CProg) :
    (cpmap (.Y :: cp)).map.node (.X : (cpmap (.Y :: cp)).Dart) = .icp .Xe :=
  PointedMap.node_ecpY (cpmap cp)

private theorem cpring_injY (cp : CProg) (h : (cpmap cp).Proper) (t : List (cpmap cp).Dart)
    (ht : (cpmap cp).cpring.drop 2 = t) :
    (cpmap (.Y :: cp)).cpring
      = (cpmap (.Y :: cp)).map.node .X :: .X
        :: (((cpmap cp).point :: t).map (injcpStep .Y cp)) := by
  have hring : (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: t := by
    rw [← ht]
    exact Hypermap.head_proper_cpring h
  have htail : (cpmap cp).cpring.tail = (cpmap cp).point :: t := by
    rw [hring]
    rfl
  have hY := PointedMap.cpring_ecpY' (cpmap cp)
  rw [htail] at hY
  exact hY

/-- A disjunct of a boolean `or` selects. -/
private theorem orLeft {a b : Bool} (h : a = true) : (a || b) = true := by
  rw [h]
  rfl

/-- A disjunct of a boolean `or` selects. -/
private theorem orRight {a b : Bool} (h : b = true) : (a || b) = true := by
  rw [h]
  cases a <;> rfl

/-- A boolean `or` selects only through one of its disjuncts. -/
private theorem orCases {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

/-- The propositional step of the `Y` case: the new face contributes exactly the
two ring faces it is adjacent to. -/
private theorem prop_Y {P0 P1 A0 A1 R3 R4 S3 S4 : Prop} {a0 a2 b0 b1 b2 : Bool}
    (h : ((a0 = true ∧ P0) ∨ (a2 = true ∧ P1) ∨ R3) ∨ R4
      ↔ ((b0 = true ∧ A0) ∨ (b2 = true ∧ A1) ∨ S3) ∨ S4) :
    ((((a0 || b1) = true ∧ P0) ∨ ((a2 || b1) = true ∧ P1) ∨ R3) ∨ R4)
      ↔ (((b0 = true ∧ A0) ∨ (b1 = true ∧ (P0 ∨ P1)) ∨ (b2 = true ∧ A1) ∨ S3) ∨ S4) := by
  have hin : (((b0 = true ∧ A0) ∨ (b2 = true ∧ A1) ∨ S3) ∨ S4) →
      (((b0 = true ∧ A0) ∨ (b1 = true ∧ (P0 ∨ P1)) ∨ (b2 = true ∧ A1) ∨ S3) ∨ S4) := by
    rintro ((hc | hc | hc) | hc)
    · exact Or.inl (Or.inl hc)
    · exact Or.inl (Or.inr (Or.inr (Or.inl hc)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr hc)))
    · exact Or.inr hc
  have hout : (((a0 = true ∧ P0) ∨ (a2 = true ∧ P1) ∨ R3) ∨ R4) →
      ((((a0 || b1) = true ∧ P0) ∨ ((a2 || b1) = true ∧ P1) ∨ R3) ∨ R4) := by
    rintro ((⟨hb, hp⟩ | ⟨hb, hp⟩ | hr) | hr)
    · exact Or.inl (Or.inl ⟨orLeft hb, hp⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨orLeft hb, hp⟩))
    · exact Or.inl (Or.inr (Or.inr hr))
    · exact Or.inr hr
  constructor
  · rintro ((⟨hb, hp⟩ | ⟨hb, hp⟩ | hr) | hr)
    · rcases orCases hb with hb' | hb'
      · exact hin (h.mp (Or.inl (Or.inl ⟨hb', hp⟩)))
      · exact Or.inl (Or.inr (Or.inl ⟨hb', Or.inl hp⟩))
    · rcases orCases hb with hb' | hb'
      · exact hin (h.mp (Or.inl (Or.inr (Or.inl ⟨hb', hp⟩))))
      · exact Or.inl (Or.inr (Or.inl ⟨hb', Or.inr hp⟩))
    · exact hin (h.mp (Or.inl (Or.inr (Or.inr hr))))
    · exact hin (h.mp (Or.inr hr))
  · rintro ((hc | ⟨hb, hp⟩ | hc | hc) | hc)
    · exact hout (h.mpr (Or.inl (Or.inl hc)))
    · rcases hp with hp | hp
      · exact Or.inl (Or.inl ⟨orRight hb, hp⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨orRight hb, hp⟩))
    · exact hout (h.mpr (Or.inl (Or.inr (Or.inl hc))))
    · exact hout (h.mpr (Or.inl (Or.inr (Or.inr hc))))
    · exact hout (h.mpr (Or.inr hc))

/-- The propositional step of the `H` case: the new face contributes exactly the
three ring faces it is adjacent to. -/
private theorem prop_H {P0 P1 P2 A0 A1 A2 R4 R6 S4 S6 : Prop}
    {a0 a1 a2 b0 b1 b1' m2 : Bool}
    (h : ((a0 = true ∧ P0) ∨ (a1 = true ∧ P1) ∨ (a2 = true ∧ P2) ∨ R4) ∨ R6
      ↔ ((b0 = true ∧ A0) ∨ (b1' = true ∧ A1) ∨ (m2 = true ∧ A2) ∨ S4) ∨ S6) :
    ((((a0 || b1) = true ∧ P0) ∨ ((a2 || b1) = true ∧ P2) ∨ R4)
        ∨ (((a1 || b1) = true ∧ P1) ∨ R6))
      ↔ (((b0 = true ∧ A0) ∨ (b1 = true ∧ (P0 ∨ P1 ∨ P2)) ∨ (m2 = true ∧ A2) ∨ S4)
        ∨ ((b1' = true ∧ A1) ∨ S6)) := by
  have hin : (((b0 = true ∧ A0) ∨ (b1' = true ∧ A1) ∨ (m2 = true ∧ A2) ∨ S4) ∨ S6) →
      (((b0 = true ∧ A0) ∨ (b1 = true ∧ (P0 ∨ P1 ∨ P2)) ∨ (m2 = true ∧ A2) ∨ S4)
        ∨ ((b1' = true ∧ A1) ∨ S6)) := by
    rintro ((hc | hc | hc | hc) | hc)
    · exact Or.inl (Or.inl hc)
    · exact Or.inr (Or.inl hc)
    · exact Or.inl (Or.inr (Or.inr (Or.inl hc)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr hc)))
    · exact Or.inr (Or.inr hc)
  have hout : (((a0 = true ∧ P0) ∨ (a1 = true ∧ P1) ∨ (a2 = true ∧ P2) ∨ R4) ∨ R6) →
      ((((a0 || b1) = true ∧ P0) ∨ ((a2 || b1) = true ∧ P2) ∨ R4)
        ∨ (((a1 || b1) = true ∧ P1) ∨ R6)) := by
    rintro ((⟨hb, hp⟩ | ⟨hb, hp⟩ | ⟨hb, hp⟩ | hr) | hr)
    · exact Or.inl (Or.inl ⟨orLeft hb, hp⟩)
    · exact Or.inr (Or.inl ⟨orLeft hb, hp⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨orLeft hb, hp⟩))
    · exact Or.inl (Or.inr (Or.inr hr))
    · exact Or.inr (Or.inr hr)
  constructor
  · rintro ((⟨hb, hp⟩ | ⟨hb, hp⟩ | hr) | (⟨hb, hp⟩ | hr))
    · rcases orCases hb with hb' | hb'
      · exact hin (h.mp (Or.inl (Or.inl ⟨hb', hp⟩)))
      · exact Or.inl (Or.inr (Or.inl ⟨hb', Or.inl hp⟩))
    · rcases orCases hb with hb' | hb'
      · exact hin (h.mp (Or.inl (Or.inr (Or.inr (Or.inl ⟨hb', hp⟩)))))
      · exact Or.inl (Or.inr (Or.inl ⟨hb', Or.inr (Or.inr hp)⟩))
    · exact hin (h.mp (Or.inl (Or.inr (Or.inr (Or.inr hr)))))
    · rcases orCases hb with hb' | hb'
      · exact hin (h.mp (Or.inl (Or.inr (Or.inl ⟨hb', hp⟩))))
      · exact Or.inl (Or.inr (Or.inl ⟨hb', Or.inr (Or.inl hp)⟩))
    · exact hin (h.mp (Or.inr hr))
  · rintro ((hc | ⟨hb, hp⟩ | hc | hc) | (hc | hc))
    · exact hout (h.mpr (Or.inl (Or.inl hc)))
    · rcases hp with hp | hp | hp
      · exact Or.inl (Or.inl ⟨orRight hb, hp⟩)
      · exact Or.inr (Or.inl ⟨orRight hb, hp⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨orRight hb, hp⟩))
    · exact hout (h.mpr (Or.inl (Or.inr (Or.inr (Or.inl hc)))))
    · exact hout (h.mpr (Or.inl (Or.inr (Or.inr (Or.inr hc)))))
    · exact hout (h.mpr (Or.inl (Or.inr (Or.inl hc))))
    · exact hout (h.mpr (Or.inr hc))

/-- **The adjacency mask of a `Y` step.** -/
private theorem cpmask_adj_Y (cp : CProg) (hsub : cp = [] ∨ ConfigProg cp)
    (b0 b1 b2 : Bool) (mr km : List Bool)
    (hprop : (⟨b0 :: b1 :: b2 :: mr, km⟩ : CfMask).Proper (.Y :: cp))
    (ih : ∀ cm : CfMask, cm.Proper cp → ∀ x : (cpmap cp).Dart,
      (cpmap cp).map.Fband (cpmask (cpadj cm cp) cp) x
        ↔ ∃ y ∈ cpmask cm cp, (cpmap cp).map.Adj x y)
    (u : (cpmap (.Y :: cp)).Dart) :
    (cpmap (.Y :: cp)).map.Fband
        (cpmask (cpadj (⟨b0 :: b1 :: b2 :: mr, km⟩ : CfMask) (.Y :: cp)) (.Y :: cp)) u
      ↔ ∃ y ∈ cpmask (⟨b0 :: b1 :: b2 :: mr, km⟩ : CfMask) (.Y :: cp),
          (cpmap (.Y :: cp)).map.Adj u y := by
  have hM : (cpmap cp).Proper := cpmap_proper' cp hsub
  have hplainY : (cpmap (.Y :: cp)).Plain := (cpmap_plain' cp hsub).ecpY
  obtain ⟨t, ht⟩ : ∃ t, (cpmap cp).cpring.drop 2 = t := ⟨_, rfl⟩
  obtain ⟨nY, hnY⟩ : ∃ w : (cpmap (.Y :: cp)).Dart, w = (cpmap (.Y :: cp)).map.node .X :=
    ⟨_, rfl⟩
  obtain ⟨xX, hxX⟩ : ∃ w : (cpmap (.Y :: cp)).Dart, w = .X := ⟨_, rfl⟩
  have hring : (cpmap cp).cpring
      = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point :: t := by
    rw [← ht]
    exact Hypermap.head_proper_cpring hM
  have hringY : (cpmap (.Y :: cp)).cpring
      = nY :: xX :: (((cpmap cp).point :: t).map (injcpStep .Y cp)) := by
    rw [hnY, hxX]
    exact cpring_injY cp hM t ht
  have hkerY : cpker (.Y :: cp) = (cpker cp).map (injcpStep .Y cp) := cpker_Y cp
  have hlen1 : mr.length + 3 = cprsize cp + 1 := hprop.1
  have hlen2 : km.length = cpksize cp := hprop.2
  have hprop2 : (⟨b0 :: b2 :: mr, km⟩ : CfMask).Proper cp := by
    refine ⟨?_, hlen2⟩
    simp only [List.length_cons]
    omega
  have hge : 2 ≤ cprsize cp := by
    have h1 := (PointedMap.proper_iff _).mp hM
    rw [size_ring_cpmap cp] at h1
    omega
  obtain ⟨a0, a2, mr', mk', hres⟩ :
      ∃ a0 a2 mr' mk', cpadj ⟨b0 :: b2 :: mr, km⟩ cp = ⟨a0 :: a2 :: mr', mk'⟩ := by
    obtain ⟨mr2, mk2, hres2⟩ : ∃ mr2 mk2, cpadj ⟨b0 :: b2 :: mr, km⟩ cp = ⟨mr2, mk2⟩ :=
      ⟨_, _, rfl⟩
    have hq := cpadj_proper cp _ hprop2
    rw [hres2] at hq
    have hl : mr2.length = cprsize cp := hq.1
    rcases mr2 with _ | ⟨d0, mr2⟩
    · simp only [List.length_nil] at hl; omega
    rcases mr2 with _ | ⟨d2, mr2⟩
    · simp only [List.length_cons, List.length_nil] at hl; omega
    exact ⟨d0, d2, mr2, mk2, hres2⟩
  have hsimple := cpmap_simple' cp hsub
  have hsimple' : (cpmap cp).map.Simple ((cpmap cp).map.node (cpmap cp).point ::
      (cpmap cp).point :: (t ++ cpker cp)) := by
    rw [← List.cons_append, ← List.cons_append, ← hring]
    exact hsimple
  obtain ⟨hnb0, hrest⟩ := Hypermap.simple_cons.mp hsimple'
  obtain ⟨hnb1, -⟩ := Hypermap.simple_cons.mp hrest
  rw [cpadj_Y_of cp b0 b1 b2 mr km a0 a2 mr' mk' hres, fband_cpmask, exists_mem_cpmask,
    hringY, hkerY]
  dsimp only
  rw [anyMask_ring, anyMask_map, anyMask_ring, anyMask_map]
  rcases fband_injY cp u with ⟨x, hx⟩ | hXu
  · have hcf : ∀ w, (cpmap (.Y :: cp)).map.CFace u w
        ↔ (cpmap (.Y :: cp)).map.CFace (injcpStep .Y cp x) w :=
      fun w => ⟨fun hc => hx.symm.trans hc, fun hc => hx.trans hc⟩
    have hadj : ∀ w, (cpmap (.Y :: cp)).map.Adj u w
        ↔ (cpmap (.Y :: cp)).map.Adj (injcpStep .Y cp x) w :=
      fun w => Hypermap.adj_congr_left hx w
    have e1 : (cpmap (.Y :: cp)).map.CFace (injcpStep .Y cp x) nY
        ↔ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point) := by
      rw [hnY, ← cface_injY cp x ((cpmap cp).map.node (cpmap cp).point)]
      exact ⟨fun hc => hc.trans (cface_node_injY cp),
        fun hc => hc.trans (cface_node_injY cp).symm⟩
    have e2 : ¬ (cpmap (.Y :: cp)).map.CFace (injcpStep .Y cp x) xX := by
      rw [hxX]
      exact fun hc => not_cface_X_injY cp x hc.symm
    have e3 : (cpmap (.Y :: cp)).map.Adj (injcpStep .Y cp x) nY
        ↔ (cpmap cp).map.Adj x ((cpmap cp).map.node (cpmap cp).point) := by
      rw [hnY, ← adj_injY cp x ((cpmap cp).map.node (cpmap cp).point)]
      exact Hypermap.adj_congr_right (cface_node_injY cp) _
    have e4 : (cpmap (.Y :: cp)).map.Adj (injcpStep .Y cp x) xX
        ↔ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point)
          ∨ (cpmap cp).map.CFace x (cpmap cp).point := by
      rw [hxX]
      constructor
      · intro hc
        rcases (adj_X_ecpY cp hM _).mp (hplainY.adj_symm hc) with hc' | hc'
        · exact Or.inl ((cface_injY cp _ _).mp hc')
        · exact Or.inr ((cface_injY cp _ _).mp hc')
      · intro hc
        refine hplainY.adj_symm ((adj_X_ecpY cp hM _).mpr ?_)
        rcases hc with hc | hc
        · exact Or.inl ((cface_injY cp _ _).mpr hc)
        · exact Or.inr ((cface_injY cp _ _).mpr hc)
    have hIHx := ih ⟨b0 :: b2 :: mr, km⟩ hprop2 x
    rw [fband_cpmask, exists_mem_cpmask] at hIHx
    rw [hres] at hIHx
    dsimp only at hIHx
    rw [hring, anyMask_cons2, anyMask_cons2] at hIHx
    simp only [hcf, hadj, e1, e2, e3, e4, cface_injY, adj_injY, and_false, false_or]
    exact prop_Y hIHx
  · have hcf : ∀ w, (cpmap (.Y :: cp)).map.CFace u w
        ↔ (cpmap (.Y :: cp)).map.CFace xX w := by
      intro w
      rw [hxX]
      exact ⟨fun hc => hXu.trans hc, fun hc => hXu.symm.trans hc⟩
    have hadj : ∀ w, (cpmap (.Y :: cp)).map.Adj u w
        ↔ (cpmap (.Y :: cp)).map.Adj xX w := by
      intro w
      rw [hxX]
      exact Hypermap.adj_congr_left hXu.symm w
    have f1 : ¬ (cpmap (.Y :: cp)).map.CFace xX nY := by
      rw [hxX, hnY, cface_X_ecpY, node_X_ecpY]
      rintro (hc | hc)
      · exact absurd hc (by simp)
      · exact absurd (EcpDart.icp_injective hc) (by simp)
    have f2 : (cpmap (.Y :: cp)).map.CFace xX xX := Equiv.Perm.SameCycle.refl _ _
    have f3 : ∀ z : (cpmap cp).Dart,
        ¬ (cpmap (.Y :: cp)).map.CFace xX (injcpStep .Y cp z) := by
      intro z
      rw [hxX]
      exact not_cface_X_injY cp z
    have g3 : ∀ z : (cpmap cp).Dart,
        (cpmap (.Y :: cp)).map.Adj xX (injcpStep .Y cp z)
          ↔ (cpmap cp).map.CFace z ((cpmap cp).map.node (cpmap cp).point)
            ∨ (cpmap cp).map.CFace z (cpmap cp).point := by
      intro z
      rw [hxX, adj_X_ecpY cp hM, cface_injY, cface_injY]
    have g1 : (cpmap (.Y :: cp)).map.Adj xX nY := by
      rw [hxX, hnY]
      exact (adj_X_ecpY cp hM _).mpr (Or.inl (cface_node_injY cp))
    have g2 : ¬ (cpmap (.Y :: cp)).map.Adj xX xX := by
      rw [hxX]
      intro hc
      rcases (adj_X_ecpY cp hM _).mp hc with hc' | hc'
      · exact not_cface_X_injY cp _ hc'
      · exact not_cface_X_injY cp _ hc'
    have g4 : (cpmap (.Y :: cp)).map.Adj xX (injcpStep .Y cp (cpmap cp).point) :=
      (g3 _).mpr (Or.inr (Equiv.Perm.SameCycle.refl _ _))
    have h5 : ¬ AnyMask (fun z : (cpmap cp).Dart =>
        (cpmap (.Y :: cp)).map.Adj xX (injcpStep .Y cp z)) mr t := by
      refine anyMask_eq_false fun z hz => ?_
      rw [g3 z]
      rintro (hc | hc)
      · exact hnb0 ⟨z, List.mem_cons_of_mem _ (List.mem_append_left _ hz), hc.symm⟩
      · exact hnb1 ⟨z, List.mem_append_left _ hz, hc.symm⟩
    have h6 : ¬ AnyMask (fun z : (cpmap cp).Dart =>
        (cpmap (.Y :: cp)).map.Adj xX (injcpStep .Y cp z)) km (cpker cp) := by
      refine anyMask_eq_false fun z hz => ?_
      rw [g3 z]
      rintro (hc | hc)
      · exact hnb0 ⟨z, List.mem_cons_of_mem _ (List.mem_append_right _ hz), hc.symm⟩
      · exact hnb1 ⟨z, List.mem_append_right _ hz, hc.symm⟩
    simp only [hcf, hadj, f1, f2, f3, g1, g2, g4, h5, h6, anyMask_false, and_true,
      and_false, false_or, or_false]
    clear * -
    cases b0 <;> cases b2 <;> simp

/-! #### Adapters for the `H` step -/

private theorem cface_injH (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (.H :: cp)).map.CFace (injcpStep .H cp x) (injcpStep .H cp y)
      ↔ (cpmap cp).map.CFace x y := PointedMap.cface_icpH' (cpmap cp) x y

private theorem adj_injH (cp : CProg) (x y : (cpmap cp).Dart) :
    (cpmap (.H :: cp)).map.Adj (injcpStep .H cp x) (injcpStep .H cp y)
      ↔ (cpmap cp).map.Adj x y := PointedMap.adj_icpH' (cpmap cp) x y

private theorem fband_injH (cp : CProg) (u : (cpmap (.H :: cp)).Dart) :
    (∃ x : (cpmap cp).Dart, (cpmap (.H :: cp)).map.CFace u (injcpStep .H cp x))
      ∨ (cpmap (.H :: cp)).map.CFace .X u := PointedMap.fband_icpH' (cpmap cp) u

private theorem not_cface_X_injH (cp : CProg) (h : (cpmap cp).Proper) (x : (cpmap cp).Dart) :
    ¬ (cpmap (.H :: cp)).map.CFace (.X : (cpmap (.H :: cp)).Dart) (injcpStep .H cp x) :=
  PointedMap.not_cface_ecpH_icpH (cpmap cp) h x

private theorem cface_node_injH (cp : CProg) (h : (cpmap cp).Proper) :
    (cpmap (.H :: cp)).map.CFace ((cpmap (.H :: cp)).map.node .X)
      (injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point)) :=
  PointedMap.cface_node_ecpH' (cpmap cp) h

private theorem adj_X_ecpH (cp : CProg) (h : (cpmap cp).Proper)
    (u : (cpmap (.H :: cp)).Dart) :
    (cpmap (.H :: cp)).map.Adj .X u
      ↔ (cpmap (.H :: cp)).map.CFace u
            (injcpStep .H cp ((cpmap cp).map.node (cpmap cp).point))
        ∨ (cpmap (.H :: cp)).map.CFace u (injcpStep .H cp (cpmap cp).point)
        ∨ (cpmap (.H :: cp)).map.CFace u
            (injcpStep .H cp ((cpmap cp).map.node⁻¹ (cpmap cp).point)) :=
  PointedMap.adj_ecpH (cpmap cp) h u

private theorem cface_X_ecpH (cp : CProg) (h : (cpmap cp).Proper)
    (u : (cpmap (.H :: cp)).Dart) :
    (cpmap (.H :: cp)).map.CFace .X u ↔ u = .X ∨ u = .icp .X ∨ u = .icp (.icp .X) :=
  PointedMap.cface_ecpH (cpmap cp) h u

private theorem node_X_ecpH (cp : CProg) (h : (cpmap cp).Proper) :
    (cpmap (.H :: cp)).map.node (.X : (cpmap (.H :: cp)).Dart) = .icp (.icp .Xe) :=
  PointedMap.node_ecpH (cpmap cp) h

private theorem cpring_injH (cp : CProg) (h : (cpmap cp).Proper) (d : List (cpmap cp).Dart)
    (hd : (cpmap cp).cpring.drop 2 = d) :
    (cpmap (.H :: cp)).cpring
      = (cpmap (.H :: cp)).map.node .X :: .X :: (d.map (injcpStep .H cp)) := by
  have hH := PointedMap.cpring_ecpH' (cpmap cp) h
  rw [hd] at hH
  exact hH

/-- Unfolding `cpadjTail` on a nonempty mask. -/
theorem cpadjTail_cons (b a : Bool) (m : List Bool) :
    cpadjTail b (a :: m) = (a || b) :: m := rfl

/-- The head of a nonempty list. -/
private theorem headD_cons' {α : Type*} (a : α) (l : List α) (dflt : α) :
    (a :: l).headD dflt = a := rfl

/-- **The adjacency mask of an `H` step.** -/
private theorem cpmask_adj_H (cp : CProg) (hcp : ConfigProg cp)
    (b0 b1 b1' : Bool) (mr km : List Bool)
    (hprop : (⟨b0 :: b1 :: mr, b1' :: km⟩ : CfMask).Proper (.H :: cp))
    (ih : ∀ cm : CfMask, cm.Proper cp → ∀ x : (cpmap cp).Dart,
      (cpmap cp).map.Fband (cpmask (cpadj cm cp) cp) x
        ↔ ∃ y ∈ cpmask cm cp, (cpmap cp).map.Adj x y)
    (u : (cpmap (.H :: cp)).Dart) :
    (cpmap (.H :: cp)).map.Fband
        (cpmask (cpadj (⟨b0 :: b1 :: mr, b1' :: km⟩ : CfMask) (.H :: cp)) (.H :: cp)) u
      ↔ ∃ y ∈ cpmask (⟨b0 :: b1 :: mr, b1' :: km⟩ : CfMask) (.H :: cp),
          (cpmap (.H :: cp)).map.Adj u y := by
  have hsub : cp = [] ∨ ConfigProg cp := Or.inr hcp
  have hM : (cpmap cp).Proper := cpmap_proper hcp.cubicProg
  have hlong : (cpmap cp).Long := cfmap_long hcp
  have hplainH : (cpmap (.H :: cp)).Plain := (cpmap_plain hcp.cubicProg).ecpH
  obtain ⟨d', hd'⟩ : ∃ d', (cpmap cp).cpring.drop 3 = d' := ⟨_, rfl⟩
  have hring : (cpmap cp).cpring = (cpmap cp).map.node (cpmap cp).point :: (cpmap cp).point
      :: (cpmap cp).map.node⁻¹ (cpmap cp).point :: d' := by
    rw [← hd', ← (cpmap cp).map.face_edge (cpmap cp).point]
    exact Hypermap.head_long_cpring hlong
  have hd2 : (cpmap cp).cpring.drop 2
      = (cpmap cp).map.node⁻¹ (cpmap cp).point :: d' := by
    rw [hring]
    rfl
  obtain ⟨nH, hnH⟩ : ∃ w : (cpmap (.H :: cp)).Dart, w = (cpmap (.H :: cp)).map.node .X :=
    ⟨_, rfl⟩
  obtain ⟨xX, hxX⟩ : ∃ w : (cpmap (.H :: cp)).Dart, w = .X := ⟨_, rfl⟩
  have hringH : (cpmap (.H :: cp)).cpring
      = nH :: xX :: ((((cpmap cp).map.node⁻¹ (cpmap cp).point :: d')).map
          (injcpStep .H cp)) := by
    rw [hnH, hxX]
    exact cpring_injH cp hM _ hd2
  have hkerH : cpker (.H :: cp)
      = ((cpmap cp).point :: cpker cp).map (injcpStep .H cp) := cpker_H_point cp hM
  have hcprsize : (cpmap cp).cpring.length = cprsize cp := size_ring_cpmap cp
  have hringlen : (cpmap cp).cpring.length = d'.length + 3 := by
    rw [hring]
    simp only [List.length_cons]
  have hlen1 : mr.length + 2 = cprsize cp := hprop.1
  have hlen2 : km.length + 1 = cpksize cp + 1 := hprop.2
  have hmrlen : mr.length = d'.length + 1 := by omega
  obtain ⟨m2, mr2, hmr⟩ : ∃ m2 mr2, mr = m2 :: mr2 := by
    rcases mr with _ | ⟨m2, mr2⟩
    · simp only [List.length_nil] at hmrlen; omega
    · exact ⟨m2, mr2, rfl⟩
  subst hmr
  have hkm : km.length = cpksize cp := by omega
  have hprop2 : (⟨b0 :: b1' :: m2 :: mr2, km⟩ : CfMask).Proper cp := by
    refine ⟨?_, hkm⟩
    simp only [List.length_cons] at hlen1 ⊢
    omega
  obtain ⟨a0, a1, a2, mr3, mk', hres⟩ :
      ∃ a0 a1 a2 mr3 mk', cpadj ⟨b0 :: b1' :: m2 :: mr2, km⟩ cp
        = ⟨a0 :: a1 :: a2 :: mr3, mk'⟩ := by
    obtain ⟨mrA, mkA, hresA⟩ :
        ∃ mrA mkA, cpadj ⟨b0 :: b1' :: m2 :: mr2, km⟩ cp = ⟨mrA, mkA⟩ := ⟨_, _, rfl⟩
    have hq := cpadj_proper cp _ hprop2
    rw [hresA] at hq
    have hl : mrA.length = cprsize cp := hq.1
    rcases mrA with _ | ⟨e0, mrA⟩
    · simp only [List.length_nil] at hl; omega
    rcases mrA with _ | ⟨e1, mrA⟩
    · simp only [List.length_cons, List.length_nil] at hl; omega
    rcases mrA with _ | ⟨e2, mrA⟩
    · simp only [List.length_cons, List.length_nil] at hl
      simp only [List.length_cons] at hlen1
      omega
    exact ⟨e0, e1, e2, mrA, mkA, hresA⟩
  have hsimple := cpmap_simple' cp hsub
  have hsimple' : (cpmap cp).map.Simple ((cpmap cp).map.node (cpmap cp).point ::
      (cpmap cp).point :: (cpmap cp).map.node⁻¹ (cpmap cp).point :: (d' ++ cpker cp)) := by
    rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← hring]
    exact hsimple
  obtain ⟨hnb0, hrest0⟩ := Hypermap.simple_cons.mp hsimple'
  obtain ⟨hnb1, hrest1⟩ := Hypermap.simple_cons.mp hrest0
  obtain ⟨hnb2, -⟩ := Hypermap.simple_cons.mp hrest1
  rw [cpadj_H_of cp b0 b1 b1' (m2 :: mr2) km a0 a1 (a2 :: mr3) mk' hres, fband_cpmask,
    exists_mem_cpmask, hringH, hkerH]
  dsimp only
  rw [cpadjTail_cons, headD_cons', anyMask_ring, anyMask_map_cons, anyMask_ring,
    anyMask_map_cons]
  rcases fband_injH cp u with ⟨x, hx⟩ | hXu
  · have hcf : ∀ w, (cpmap (.H :: cp)).map.CFace u w
        ↔ (cpmap (.H :: cp)).map.CFace (injcpStep .H cp x) w :=
      fun w => ⟨fun hc => hx.symm.trans hc, fun hc => hx.trans hc⟩
    have hadj : ∀ w, (cpmap (.H :: cp)).map.Adj u w
        ↔ (cpmap (.H :: cp)).map.Adj (injcpStep .H cp x) w :=
      fun w => Hypermap.adj_congr_left hx w
    have e1 : (cpmap (.H :: cp)).map.CFace (injcpStep .H cp x) nH
        ↔ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point) := by
      rw [hnH, ← cface_injH cp x ((cpmap cp).map.node (cpmap cp).point)]
      exact ⟨fun hc => hc.trans (cface_node_injH cp hM),
        fun hc => hc.trans (cface_node_injH cp hM).symm⟩
    have e2 : ¬ (cpmap (.H :: cp)).map.CFace (injcpStep .H cp x) xX := by
      rw [hxX]
      exact fun hc => not_cface_X_injH cp hM x hc.symm
    have e3 : (cpmap (.H :: cp)).map.Adj (injcpStep .H cp x) nH
        ↔ (cpmap cp).map.Adj x ((cpmap cp).map.node (cpmap cp).point) := by
      rw [hnH, ← adj_injH cp x ((cpmap cp).map.node (cpmap cp).point)]
      exact Hypermap.adj_congr_right (cface_node_injH cp hM) _
    have e4 : (cpmap (.H :: cp)).map.Adj (injcpStep .H cp x) xX
        ↔ (cpmap cp).map.CFace x ((cpmap cp).map.node (cpmap cp).point)
          ∨ (cpmap cp).map.CFace x (cpmap cp).point
          ∨ (cpmap cp).map.CFace x ((cpmap cp).map.node⁻¹ (cpmap cp).point) := by
      rw [hxX]
      constructor
      · intro hc
        rcases (adj_X_ecpH cp hM _).mp (hplainH.adj_symm hc) with hc' | hc' | hc'
        · exact Or.inl ((cface_injH cp _ _).mp hc')
        · exact Or.inr (Or.inl ((cface_injH cp _ _).mp hc'))
        · exact Or.inr (Or.inr ((cface_injH cp _ _).mp hc'))
      · intro hc
        refine hplainH.adj_symm ((adj_X_ecpH cp hM _).mpr ?_)
        rcases hc with hc | hc | hc
        · exact Or.inl ((cface_injH cp _ _).mpr hc)
        · exact Or.inr (Or.inl ((cface_injH cp _ _).mpr hc))
        · exact Or.inr (Or.inr ((cface_injH cp _ _).mpr hc))
    have hIHx := ih ⟨b0 :: b1' :: m2 :: mr2, km⟩ hprop2 x
    rw [fband_cpmask, exists_mem_cpmask] at hIHx
    rw [hres] at hIHx
    dsimp only at hIHx
    rw [hring, anyMask_cons3, anyMask_cons3] at hIHx
    simp only [hcf, hadj, e1, e2, e3, e4, cface_injH, adj_injH, and_false, false_or]
    exact prop_H hIHx
  · have hcf : ∀ w, (cpmap (.H :: cp)).map.CFace u w
        ↔ (cpmap (.H :: cp)).map.CFace xX w := by
      intro w
      rw [hxX]
      exact ⟨fun hc => hXu.trans hc, fun hc => hXu.symm.trans hc⟩
    have hadj : ∀ w, (cpmap (.H :: cp)).map.Adj u w
        ↔ (cpmap (.H :: cp)).map.Adj xX w := by
      intro w
      rw [hxX]
      exact Hypermap.adj_congr_left hXu.symm w
    have f1 : ¬ (cpmap (.H :: cp)).map.CFace xX nH := by
      rw [hxX, hnH, cface_X_ecpH cp hM, node_X_ecpH cp hM]
      rintro (hc | hc | hc)
      · exact absurd hc (by simp)
      · exact absurd (EcpDart.icp_injective hc) (by simp)
      · exact absurd (EcpDart.icp_injective (EcpDart.icp_injective hc)) (by simp)
    have f2 : (cpmap (.H :: cp)).map.CFace xX xX := Equiv.Perm.SameCycle.refl _ _
    have f3 : ∀ z : (cpmap cp).Dart,
        ¬ (cpmap (.H :: cp)).map.CFace xX (injcpStep .H cp z) := by
      intro z
      rw [hxX]
      exact not_cface_X_injH cp hM z
    have g3 : ∀ z : (cpmap cp).Dart,
        (cpmap (.H :: cp)).map.Adj xX (injcpStep .H cp z)
          ↔ (cpmap cp).map.CFace z ((cpmap cp).map.node (cpmap cp).point)
            ∨ (cpmap cp).map.CFace z (cpmap cp).point
            ∨ (cpmap cp).map.CFace z ((cpmap cp).map.node⁻¹ (cpmap cp).point) := by
      intro z
      rw [hxX, adj_X_ecpH cp hM, cface_injH, cface_injH, cface_injH]
    have g1 : (cpmap (.H :: cp)).map.Adj xX nH := by
      rw [hxX, hnH]
      exact (adj_X_ecpH cp hM _).mpr (Or.inl (cface_node_injH cp hM))
    have g2 : ¬ (cpmap (.H :: cp)).map.Adj xX xX := by
      rw [hxX]
      intro hc
      rcases (adj_X_ecpH cp hM _).mp hc with hc' | hc' | hc'
      · exact not_cface_X_injH cp hM _ hc'
      · exact not_cface_X_injH cp hM _ hc'
      · exact not_cface_X_injH cp hM _ hc'
    have g4 : (cpmap (.H :: cp)).map.Adj xX
        (injcpStep .H cp ((cpmap cp).map.node⁻¹ (cpmap cp).point)) :=
      (g3 _).mpr (Or.inr (Or.inr (Equiv.Perm.SameCycle.refl _ _)))
    have g5 : (cpmap (.H :: cp)).map.Adj xX (injcpStep .H cp (cpmap cp).point) :=
      (g3 _).mpr (Or.inr (Or.inl (Equiv.Perm.SameCycle.refl _ _)))
    have h5 : ¬ AnyMask (fun z : (cpmap cp).Dart =>
        (cpmap (.H :: cp)).map.Adj xX (injcpStep .H cp z)) mr2 d' := by
      refine anyMask_eq_false fun z hz => ?_
      rw [g3 z]
      rintro (hc | hc | hc)
      · exact hnb0 ⟨z, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_left _ hz)), hc.symm⟩
      · exact hnb1 ⟨z, List.mem_cons_of_mem _ (List.mem_append_left _ hz), hc.symm⟩
      · exact hnb2 ⟨z, List.mem_append_left _ hz, hc.symm⟩
    have h6 : ¬ AnyMask (fun z : (cpmap cp).Dart =>
        (cpmap (.H :: cp)).map.Adj xX (injcpStep .H cp z)) km (cpker cp) := by
      refine anyMask_eq_false fun z hz => ?_
      rw [g3 z]
      rintro (hc | hc | hc)
      · exact hnb0 ⟨z, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_right _ hz)), hc.symm⟩
      · exact hnb1 ⟨z, List.mem_cons_of_mem _ (List.mem_append_right _ hz), hc.symm⟩
      · exact hnb2 ⟨z, List.mem_append_right _ hz, hc.symm⟩
    simp only [hcf, hadj, f1, f2, f3, g1, g2, g4, g5, h5, h6, anyMask_false, and_true,
      and_false, false_or, or_false]
    clear * -
    cases b0 <;> cases b1' <;> cases m2 <;> simp

/-- The faces of the initial hypermap are its two darts. -/
theorem cface_cpmap0Map (x y : Bool) : PointedMap.cpmap0Map.CFace x y ↔ x = y :=
  cface_cpmap0 x y

/-- The two faces of the initial hypermap are adjacent. -/
theorem adj_cpmap0Map (x y : Bool) : PointedMap.cpmap0Map.Adj x y ↔ y = !x :=
  adj_cpmap0 x y

/-- The adjacency mask of the empty program swaps the two ring bits. -/
private theorem cpmask_adj_nil (b0 b1 u : Bool) :
    (∃ y ∈ listMask [b1, b0] [false, true] ++ listMask ([] : List Bool) ([] : List Bool),
        PointedMap.cpmap0Map.CFace u y)
      ↔ (∃ y ∈ listMask [b0, b1] [false, true]
            ++ listMask ([] : List Bool) ([] : List Bool),
          PointedMap.cpmap0Map.Adj u y) := by
  cases b0 <;> cases b1 <;> cases u <;>
    simp [listMask, cface_cpmap0Map, adj_cpmap0Map]

/-- **The adjacency mask is correct**: a dart lies on a face selected by
`cpadj cm cp` exactly when it is adjacent to a face selected by `cm`. -/
private theorem cpmask_adj_aux : ∀ (cp : CProg), (cp = [] ∨ ConfigProg cp) →
    ∀ cm : CfMask, cm.Proper cp → ∀ u : (cpmap cp).Dart,
      (cpmap cp).map.Fband (cpmask (cpadj cm cp) cp) u
        ↔ ∃ y ∈ cpmask cm cp, (cpmap cp).map.Adj u y := by
  intro cp
  induction cp with
  | nil =>
    rintro - ⟨mr, km⟩ ⟨h1, h2⟩ u
    have h1' : mr.length = 2 := h1
    have hk : km = [] := List.eq_nil_of_length_eq_zero h2
    subst hk
    obtain ⟨b0, b1, hmr⟩ : ∃ b0 b1, mr = [b0, b1] := by
      rcases mr with _ | ⟨b0, mr⟩
      · simp at h1'
      rcases mr with _ | ⟨b1, mr⟩
      · simp at h1'
      rcases mr with _ | ⟨b2, mr⟩
      · exact ⟨b0, b1, rfl⟩
      · simp at h1'
    subst hmr
    have hring : (cpmap []).cpring = [false, true] := PointedMap.cpring_cpmap0
    have hker : cpker ([] : CProg) = [] := rfl
    have hmask1 : cpmask (cpadj (⟨[b0, b1], []⟩ : CfMask) []) []
        = listMask [b1, b0] ((cpmap []).cpring)
          ++ listMask ([] : List Bool) (cpker []) := by
      rw [cpadj_nil]
      rfl
    have hmask2 : cpmask (⟨[b0, b1], []⟩ : CfMask) []
        = listMask [b0, b1] ((cpmap []).cpring)
          ++ listMask ([] : List Bool) (cpker []) := rfl
    rw [hmask1, hmask2, hring, hker]
    exact cpmask_adj_nil b0 b1 u
  | cons s cp ih =>
    rintro h ⟨mr, km⟩ hcm u
    have hcfg : ConfigProg (s :: cp) := by
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h
    have hs := hcfg.1 s List.mem_cons_self
    have hsub : cp = [] ∨ ConfigProg cp := by
      by_cases hnil : cp = []
      · exact Or.inl hnil
      · exact Or.inr (hcfg.of_cons hnil)
    have hge : 2 ≤ cprsize cp := by
      have h1 := (PointedMap.proper_iff _).mp (cpmap_proper' cp hsub)
      rw [size_ring_cpmap cp] at h1
      omega
    cases s with
    | R n =>
      have hr1 : mr.length = cprsize cp := hcm.1
      have hlenR : mr.length = (cpmap cp).cpring.length := by
        rw [size_ring_cpmap cp]
        exact hr1
      have hprop2 : (⟨rotrMask n mr, km⟩ : CfMask).Proper cp := by
        refine ⟨?_, hcm.2⟩
        rw [length_rotrMask]
        exact hr1
      have hIH := ih hsub ⟨rotrMask n mr, km⟩ hprop2 u
      have hlenA : ((cpadj (⟨rotrMask n mr, km⟩ : CfMask) cp).ring).length
          = (cpmap cp).cpring.length := by
        rw [(cpadj_proper cp _ hprop2).1, size_ring_cpmap cp]
      have hlenB : (rotrMask n mr).length = (cpmap cp).cpring.length := by
        rw [length_rotrMask]
        exact hlenR
      have hA : (cpmask (cpadj (⟨mr, km⟩ : CfMask) (.R n :: cp)) (.R n :: cp)).Perm
          (cpmask (cpadj (⟨rotrMask n mr, km⟩ : CfMask) cp) cp) := by
        rw [cpadj_R]
        exact cpmask_rotate_perm n cp _ _ hlenA
      have hB : (cpmask (⟨mr, km⟩ : CfMask) (.R n :: cp)).Perm
          (cpmask (⟨rotrMask n mr, km⟩ : CfMask) cp) := by
        conv_lhs => rw [← rotate_rotrMask n mr]
        exact cpmask_rotate_perm n cp _ _ hlenB
      exact (fband_perm hA u).trans (hIH.trans (exists_mem_perm hB).symm)
    | R' => exact hs.elim
    | Y =>
      have hr1 : mr.length = cprsize cp + 1 := hcm.1
      obtain ⟨b0, b1, b2, mr', hmr⟩ : ∃ b0 b1 b2 mr', mr = b0 :: b1 :: b2 :: mr' := by
        rcases mr with _ | ⟨b0, mr⟩
        · simp only [List.length_nil] at hr1; omega
        rcases mr with _ | ⟨b1, mr⟩
        · simp only [List.length_cons, List.length_nil] at hr1; omega
        rcases mr with _ | ⟨b2, mr⟩
        · simp only [List.length_cons, List.length_nil] at hr1; omega
        · exact ⟨b0, b1, b2, mr, rfl⟩
      subst hmr
      exact cpmask_adj_Y cp hsub b0 b1 b2 mr' km hcm (fun cm' hcm' x => ih hsub cm' hcm' x) u
    | H =>
      have hnil : cp ≠ [] := by
        rintro rfl
        exact absurd hcfg.2 (by simp)
      have hcp := hcfg.of_cons hnil
      have hr1 : mr.length = cprsize cp := hcm.1
      have hr2 : km.length = cpksize cp + 1 := hcm.2
      obtain ⟨b0, b1, mr', hmr⟩ : ∃ b0 b1 mr', mr = b0 :: b1 :: mr' := by
        rcases mr with _ | ⟨b0, mr⟩
        · simp only [List.length_nil] at hr1; omega
        rcases mr with _ | ⟨b1, mr⟩
        · simp only [List.length_cons, List.length_nil] at hr1; omega
        · exact ⟨b0, b1, mr, rfl⟩
      obtain ⟨b1', km', hkm⟩ : ∃ b1' km', km = b1' :: km' := by
        rcases km with _ | ⟨b1', km⟩
        · simp only [List.length_nil] at hr2; omega
        · exact ⟨b1', km, rfl⟩
      subst hmr
      subst hkm
      exact cpmask_adj_H cp hcp b0 b1 b1' mr' km' hcm
        (fun cm' hcm' x => ih hsub cm' hcm' x) u
    | U => exact hs.elim
    | K => exact hs.elim
    | A => exact hs.elim

/-- **The adjacency mask is correct**: the faces selected by `cpadj cm cp` are
exactly the faces adjacent to a face selected by `cm`. -/
theorem cpmask_adj {cp : CProg} (hcp : ConfigProg cp) {cm : CfMask}
    (hcm : cm.Proper cp) (u : (cpmap cp).Dart) :
    (cpmap cp).map.Fband (cpmask (cpadj cm cp) cp) u
      ↔ ∃ y ∈ cpmask cm cp, (cpmap cp).map.Adj u y :=
  cpmask_adj_aux cp (Or.inr hcp) cm hcm u

end FourColor

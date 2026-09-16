import FourColor.CfContract
import FourColor.Kempe
import FourColor.KempeTree

/-!
# The reducibility decision procedure

The last computational step of the development: a configuration is checked for
C-reducibility by comparing two trees of traces.  Only C-reducibility is used,
since the source data for D-reducible configurations has been completed with an
arbitrary contraction.

## Main definitions

* `kempeTree cp` — the tree of the Kempe co-closure of the ring traces of the
  map built by `cp`, the reference's `Kempe_tree`.
* `kempeTreeDepth d cp` — the tree the Kempe closure loop returns after `d`
  rounds, rather than the `cprsize cp` rounds that guarantee convergence.
* `checkReducible cf` — the decidable check: `contractCtree cf` succeeds and
  returns a tree disjoint from `kempeTree cf.prog`.
* `checkReducibleAt d cf` — the same check run against `kempeTreeDepth d`.
* `CfReducible cf` — the semantic statement that `cfmap cf` is C-reducible with
  the contract `cfcontract cf`.
* `ReducibleInRange j₁ j₂ cfs` — all configurations in the range `[j₁, j₂)` of
  `cfs` are reducible.

## Main results

* `not_mem_kempeTree_iff` — the specification of `kempeTree`, the reference's
  `Kempe_treeP`.
* `kempeCoclosure_of_not_mem_kempeTreeDepth` — the one direction of that
  specification that survives at an arbitrary depth, and the only one the check
  uses.
* `check_reducible_valid` — **the check is sound**: `checkReducible cf` implies
  `CfReducible cf`.
* `check_reducible_valid_at` — **the truncated check is sound too**:
  `checkReducibleAt d cf` implies `CfReducible cf`, at any depth `d`.
* `check_reducible_in_range`, `cat_reducible_range` — the scaffolding used by
  the reducibility job files: the first turns a finite conjunction of
  `checkReducible` evaluations into a `ReducibleInRange` statement, the second
  glues contiguous ranges.
* `check_reducible_in_range_at` — the first of those at a chosen depth.

## References

Gonthier's `theories/proof/cfreducible.v`; the chromogram rotation it uses
lives in `theories/proof/kempe.v`.
-/

namespace FourColor

open Color

/-! ### Rotating a Kempe co-closure

The reference's proof rotates the trace by one and transports the Kempe-closed
predicate along that rotation with `gram_rot`.  Everything needed is already
available: `gramRot` and `matchg_gramRot` from the Kempe closure development. -/

/-- Moving the head of a list to its back is the one-step rotation. -/
private theorem rotate_one_cons {α : Type*} (a : α) (l : List α) :
    (a :: l).rotate 1 = l ++ [a] := by
  rw [List.rotate_cons_succ, List.rotate_zero]

/-- A nonempty trace that sums to zero is the rotation of the completion of its
tail.  This is the reference's `rot 1 et = ctrace (behead et)`. -/
private theorem rotate_one_eq_completeTrace {et : List Color} (hne : et ≠ [])
    (hsum : et.sum = 0) : et.rotate 1 = completeTrace et.tail := by
  cases et with
  | nil => exact absurd rfl hne
  | cons e t =>
    rw [List.sum_cons] at hsum
    rw [rotate_one_cons, List.tail_cons, completeTrace, Color.add_eq_zero_iff.mp hsum]

/-- Rotating a predicate on traces by one step, backwards: `rotatedBack P` holds
of the traces that are one-step rotations of traces satisfying `P`. -/
private def rotatedBack (P : List Color → Prop) (et : List Color) : Prop :=
  ∃ es, es.rotate 1 = et ∧ P es

/-- Kempe closure is stable under rotating the predicate.  This is where the
chromogram rotation `gramRot` is used. -/
private theorem kempeClosed_rotatedBack {P : List Color → Prop} (hP : KempeClosed P) :
    KempeClosed (rotatedBack P) := by
  rintro et1 ⟨es, rfl, hes⟩
  obtain ⟨hperm, w, hw, hw'⟩ := hP es hes
  refine ⟨fun g => ⟨es.map g, by rw [List.map_rotate], hperm g⟩, gramRot w, ?_, ?_⟩
  · rw [matchg_gramRot]; exact hw
  · intro et2 h2
    obtain ⟨es2, rfl⟩ := Hypermap.exists_rotate_one et2
    rw [matchg_gramRot] at h2
    exact ⟨es2, rfl, hw' es2 h2⟩

/-- **Transporting a Kempe co-closure of ring traces along a rotation of the
ring.**  This is the step of the reference's `check_reducible_valid` that
rotates the trace and carries the Kempe-closed predicate along. -/
private theorem kempeCoclosure_of_rotate {D : Type*} {G : Hypermap D} {r : List D}
    {et : List Color}
    (h : KempeCoclosure (G.RingTrace (r.rotate 1)) (et.rotate 1)) :
    KempeCoclosure (G.RingTrace r) et := by
  intro P hP hPet
  obtain ⟨et', ⟨k, hk, hD⟩, es', hes', hPes'⟩ :=
    h (rotatedBack P) (kempeClosed_rotatedBack hP) ⟨et, rfl, hPet⟩
  refine ⟨es', ⟨k, hk, ?_⟩, hPes'⟩
  refine List.rotate_injective 1 ?_
  change es'.rotate 1 = (trace (r.map k)).rotate 1
  rw [hes', hD, List.map_rotate, trace_rotate]

/-! ### The Kempe closure tree of a construction program -/

/-- The tree of the Kempe co-closure of the ring traces of `cpmap cp`: the
reference's `Kempe_tree`. -/
def kempeTree (cp : CProg) : Ctree := kempeTreeAt (cprsize cp) (cpcolor cp)

/-- The Kempe closure tree of a ring of the given size after `d` rounds of the
closure loop, restricted by `ctr`: the depth-parameterised `kempeTreeAt`. -/
def kempeTreeDepthAt (d : ℕ) : ℕ → Ctree → Ctree
  | h + 2, ctr => kempeTreeOfDepth h d ctr
  | _, _ => .empty

/-- Unfolding `kempeTreeDepthAt` at a ring of size `h + 2`. -/
@[simp] theorem kempeTreeDepthAt_add_two (d h : ℕ) (ctr : Ctree) :
    kempeTreeDepthAt d (h + 2) ctr = kempeTreeOfDepth h d ctr := rfl

/-- **The depth-`d` analogue of `kempeTree`**: the tree the Kempe closure loop
returns after `d` rounds instead of the `cprsize cp` rounds that guarantee
convergence.  Only soundness — a trace absent from the tree lies in the Kempe
co-closure — survives at an arbitrary depth, and soundness is all the
reducibility check uses, so `d` may be chosen to suit the computation. -/
def kempeTreeDepth (d : ℕ) (cp : CProg) : Ctree :=
  kempeTreeDepthAt d (cprsize cp) (cpcolor cp)

/-- The Kempe closure tree of a ring of size `h + 2` after `n` cycles of the
plain iteration, restricted by `ctr`. -/
def kempeTreeIterAt (n : ℕ) : ℕ → Ctree → Ctree
  | h + 2, ctr => kempeTreeIter h n ctr
  | _, _ => .empty

/-- Unfolding `kempeTreeIterAt` at a ring of size `h + 2`. -/
@[simp] theorem kempeTreeIterAt_add_two (n h : ℕ) (ctr : Ctree) :
    kempeTreeIterAt n (h + 2) ctr = kempeTreeIter h n ctr := rfl

/-- **The iterated analogue of `kempeTree`**: the tree left after `n` cycles of
the closure loop run as a plain iteration, rather than the fuel scheme's
`3 ^ d` cycles.  Only soundness survives, and soundness is all the reducibility
check uses, so `n` may be chosen to suit the computation. -/
def kempeTreeNum (n : ℕ) (cp : CProg) : Ctree :=
  kempeTreeIterAt n (cprsize cp) (cpcolor cp)

/-- The truncated loop at the full depth is the full loop. -/
theorem kempeTreeDepthAt_self : ∀ (n : ℕ) (ctr : Ctree),
    kempeTreeDepthAt n n ctr = kempeTreeAt n ctr
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, _ => rfl

/-- **`kempeTreeDepth` agrees with `kempeTree` at the full depth**, the ring
size of the program. -/
theorem kempeTreeDepth_cprsize (cp : CProg) :
    kempeTreeDepth (cprsize cp) cp = kempeTree cp :=
  kempeTreeDepthAt_self (cprsize cp) (cpcolor cp)

/-- The ring of a construction program has either one dart or at least two. -/
private theorem cprsize_eq_one_or_add_two (cp : CProg) :
    cprsize cp = 1 ∨ ∃ h, cprsize cp = h + 2 := by
  have hsize : (cpmap cp).cpring.length = cprsize cp := size_ring_cpmap cp
  have hpos : 0 < cprsize cp := by rw [← hsize]; exact Hypermap.length_cpring_pos
  rcases Nat.lt_or_ge (cprsize cp) 2 with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr ⟨cprsize cp - 2, by omega⟩

/-- **The soundness half of the specification of `cpcolor`**, in the shape the
Kempe closure loop consumes: every trace of the tree has length one less than
the ring, and completes to a ring trace of the once-rotated ring. -/
private theorem ringTrace_of_mem_cpcolor {cp : CProg} {h : ℕ} (hn : cprsize cp = h + 2) :
    ∀ e : List Color, Ctree.mem (cpcolor cp) e →
      (cpmap cp).map.RingTrace ((cpmap cp).cpring.rotate 1) (completeTrace e)
        ∧ e.length = h + 1 := by
  have hsize : (cpmap cp).cpring.length = cprsize cp := size_ring_cpmap cp
  intro e he
  obtain ⟨-, k, hk, hDet⟩ := (ctree_mem_cpcolor cp e).mp he
  have hle : e.length + 1 = cprsize cp := by
    have := congrArg List.length hDet
    simpa [hsize] using this
  refine ⟨⟨k, hk, ?_⟩, by omega⟩
  rw [List.map_rotate, trace_rotate, ← hDet, rotate_one_cons, completeTrace]

/-- **The completeness half of the specification of `cpcolor`**: every ring
trace of the once-rotated ring occurs, in even form, in the tree. -/
private theorem mem_cpcolor_of_ringTrace (cp : CProg) : ∀ e : List Color,
    (cpmap cp).map.RingTrace ((cpmap cp).cpring.rotate 1) (completeTrace e) →
      Ctree.mem (cpcolor cp) (evenize e) := by
  intro e he
  obtain ⟨k, hk, hD⟩ := he
  have heq : e.sum :: e = trace ((cpmap cp).cpring.map k) := by
    refine List.rotate_injective 1 ?_
    change (e.sum :: e).rotate 1 = (trace ((cpmap cp).cpring.map k)).rotate 1
    rw [rotate_one_cons, ← completeTrace, hD, List.map_rotate, trace_rotate]
  refine (ctree_mem_cpcolor cp (evenize e)).mpr ⟨evenTrace_evenize e, ?_⟩
  refine ⟨(evenPerm e : Color → Color) ∘ k,
    hk.comp (EdgePerm.apply_injective (evenPerm e)), ?_⟩
  simp only [evenize]
  rw [← List.map_map, trace_map, ← heq, List.map_cons, map_sum]

/-- The one-element trace of a ring of one dart lies in every Kempe co-closure:
no chromogram matches it, so a Kempe-closed predicate cannot get started. -/
private theorem kempeCoclosure_completeTrace_nil {P : List Color → Prop} :
    KempeCoclosure P (completeTrace []) := by
  intro P' hP' hPet
  obtain ⟨-, w, hw, -⟩ := hP' _ hPet
  exact absurd (List.mem_singleton.mpr rfl)
    (matchg_notMem_zero (completeTrace []) [] w hw)

/-- **The specification of `kempeTree`**, the reference's `Kempe_treeP`: an even
trace of the ring size minus one is absent from `kempeTree cp` exactly when its
completion lies in the Kempe co-closure of the ring traces of the once-rotated
ring of `cpmap cp`. -/
theorem not_mem_kempeTree_iff (cp : CProg) {et : List Color}
    (hlen : et.length = cprsize cp - 1) :
    Ctree.mem (kempeTree cp) (evenize et) = false ↔
      KempeCoclosure ((cpmap cp).map.RingTrace ((cpmap cp).cpring.rotate 1))
        (completeTrace et) := by
  rcases cprsize_eq_one_or_add_two cp with hn | ⟨h, hn⟩
  · -- A ring of one dart: the tree is empty and the co-closure holds vacuously,
    -- since no chromogram matches the one-element trace `[c0]`.
    have hnil : et = [] := List.length_eq_zero_iff.mp (by rw [hlen, hn])
    have hempty : kempeTree cp = .empty := by rw [kempeTree, hn]; rfl
    rw [hempty, Ctree.mem_empty, hnil]
    exact iff_of_true rfl kempeCoclosure_completeTrace_nil
  · -- The general case: the specification of `cpcolor` feeds the Kempe closure.
    have hlen' : et.length = h + 1 := by omega
    have := not_mem_kempeTreeAt_iff (ringTrace_of_mem_cpcolor hn)
      (mem_cpcolor_of_ringTrace cp) hlen'
    rw [kempeTree, hn]
    exact this

/-- **The specification of `kempeTreeDepth`**: the direction of
`not_mem_kempeTree_iff` that the reducibility check uses, at an arbitrary depth.
An even trace of the ring size minus one that is absent from the depth-`d` tree
completes to a trace in the Kempe co-closure of the ring traces of the
once-rotated ring.  Unlike the converse, this rests on the invariant of the
closure loop alone, not on the loop having run to convergence. -/
theorem kempeCoclosure_of_not_mem_kempeTreeDepth {d : ℕ} (cp : CProg) {et : List Color}
    (hlen : et.length = cprsize cp - 1)
    (hmem : Ctree.mem (kempeTreeDepth d cp) (evenize et) = false) :
    KempeCoclosure ((cpmap cp).map.RingTrace ((cpmap cp).cpring.rotate 1))
      (completeTrace et) := by
  rcases cprsize_eq_one_or_add_two cp with hn | ⟨h, hn⟩
  · -- A ring of one dart: the co-closure holds vacuously, as for `kempeTree`.
    have hnil : et = [] := List.length_eq_zero_iff.mp (by rw [hlen, hn])
    rw [hnil]
    exact kempeCoclosure_completeTrace_nil
  · -- The general case: only the soundness half of `cpcolor` is needed.
    have hlen' : et.length = h + 1 := by omega
    rw [kempeTreeDepth, hn, kempeTreeDepthAt_add_two] at hmem
    exact kempeCoclosure_of_not_mem_depth (ringTrace_of_mem_cpcolor hn) hlen' hmem

/-- **The specification of `kempeTreeNum`**: the soundness direction of
`not_mem_kempeTree_iff` after any number of cycles of the plain iteration. -/
theorem kempeCoclosure_of_not_mem_kempeTreeNum {n : ℕ} (cp : CProg) {et : List Color}
    (hlen : et.length = cprsize cp - 1)
    (hmem : Ctree.mem (kempeTreeNum n cp) (evenize et) = false) :
    KempeCoclosure ((cpmap cp).map.RingTrace ((cpmap cp).cpring.rotate 1))
      (completeTrace et) := by
  rcases cprsize_eq_one_or_add_two cp with hn | ⟨h, hn⟩
  · -- A ring of one dart: the co-closure holds vacuously, as for `kempeTree`.
    have hnil : et = [] := List.length_eq_zero_iff.mp (by rw [hlen, hn])
    rw [hnil]
    exact kempeCoclosure_completeTrace_nil
  · -- The general case: only the soundness half of `cpcolor` is needed.
    have hlen' : et.length = h + 1 := by omega
    rw [kempeTreeNum, hn] at hmem
    exact kempeCoclosure_of_not_mem_iter (n := n) (ringTrace_of_mem_cpcolor hn) hlen' hmem

/-! ### The reducibility check -/

/-- `checkReducible cf` is the C-reducibility check: the configuration program
is well formed with a valid contract, and the tree of the contract colourings
returned by `contractCtree` is disjoint from the tree of the Kempe co-closure of
the colourings of `cfmap cf`. -/
def checkReducible (cf : Config) : Bool :=
  (contractCtree cf).elim false (Ctree.disjoint (kempeTree cf.prog))

/-- `checkReducibleAt d cf` is the reducibility check of `checkReducible` run
against the depth-`d` Kempe closure tree.  It is a weaker test — the tree is
larger, so disjointness is harder to obtain — but it is just as sound, and far
cheaper to evaluate. -/
def checkReducibleAt (d : ℕ) (cf : Config) : Bool :=
  (contractCtree cf).elim false (Ctree.disjoint (kempeTreeDepth d cf.prog))

/-- `checkReducibleNum n cf` is the reducibility check run against the tree left
by `n` cycles of the plain closure iteration.  The reference's fuel scheme needs
`3 ^ d` cycles to reach the same point that `n` cycles of this one reach, so for
the same amount of closure this is exponentially cheaper. -/
def checkReducibleNum (n : ℕ) (cf : Config) : Bool :=
  (contractCtree cf).elim false (Ctree.disjoint (kempeTreeNum n cf.prog))

/-- `CfReducible cf` says that `cfmap cf` is semantically C-reducible with the
contract `cfcontract cf`. -/
def CfReducible (cf : Config) : Prop :=
  (cfmap cf).map.CReducible (cfring cf) (cfcontract cf)

/-- **The shared body of the soundness proofs of the reducibility checks.**
Any tree `T` disjoint from the contract tree certifies C-reducibility, provided
the traces it misses lie in the Kempe co-closure of the ring traces of the
once-rotated ring — which is exactly what `not_mem_kempeTree_iff` gives for
`kempeTree`, and `kempeCoclosure_of_not_mem_kempeTreeDepth` for
`kempeTreeDepth`. -/
theorem check_reducible_valid_of_coclosure {cf : Config} {T : Ctree}
    (hchk : (contractCtree cf).elim false (Ctree.disjoint T) = true)
    (hco : ∀ et : List Color, et.length = cprsize cf.prog - 1 →
      Ctree.mem T (evenize et) = false →
        KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1))
          (completeTrace et)) :
    CfReducible cf := by
  rcases hc : contractCtree cf with _ | cct
  · rw [hc] at hchk; exact absurd hchk (by simp)
  rw [hc] at hchk
  simp only [Option.elim] at hchk
  obtain ⟨hvalid, hcol⟩ := contract_ctreeP hc
  refine ⟨hvalid, ?_⟩
  intro et htr
  have hmem := Ctree.mem_eq_false_of_disjoint hchk (hcol et htr)
  have hsize : (cfmap cf).cpring.length = cprsize cf.prog := size_ring_cpmap cf.prog
  have hrr : (cfring cf).reverse = (cfmap cf).cpring := List.reverse_reverse _
  obtain ⟨k, hk, hDet⟩ := htr
  rw [hrr] at hDet
  have hlen : et.length = cprsize cf.prog := by
    rw [hDet]; simpa using hsize
  have hpos : 0 < cprsize cf.prog := by rw [← hsize]; exact Hypermap.length_cpring_pos
  have hne : et ≠ [] := by
    intro h0
    rw [h0, List.length_nil] at hlen
    omega
  have hsum : et.sum = 0 := by rw [hDet]; exact sum_trace _
  have hlen' : et.tail.length = cprsize cf.prog - 1 := by
    rw [List.length_tail, hlen]
  have hcot : KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1))
      (et.rotate 1) := by
    rw [rotate_one_eq_completeTrace hne hsum]
    exact hco et.tail hlen' hmem
  rw [hrr]
  exact kempeCoclosure_of_rotate hcot

/-- **The reducibility check is sound.**  This is the bridge between the
computational reducibility checks and the mathematical theory: a configuration
that passes `checkReducible` really is C-reducible. -/
theorem check_reducible_valid {cf : Config} (hchk : checkReducible cf = true) :
    CfReducible cf := by
  rw [checkReducible] at hchk
  exact check_reducible_valid_of_coclosure hchk fun et hlen hmem =>
    (not_mem_kempeTree_iff cf.prog hlen).mp hmem

/-- **The truncated reducibility check is sound too**, at every depth: a
configuration that passes `checkReducibleAt d` is C-reducible.  Only the
soundness half of the specification of the Kempe closure tree is used, so the
loop need not have run to convergence — which is what makes the check
affordable. -/
theorem check_reducible_valid_at {d : ℕ} {cf : Config}
    (hchk : checkReducibleAt d cf = true) : CfReducible cf := by
  rw [checkReducibleAt] at hchk
  exact check_reducible_valid_of_coclosure hchk fun et hlen hmem =>
    kempeCoclosure_of_not_mem_kempeTreeDepth cf.prog hlen hmem

/-- **The iterated reducibility check is sound too**, after any number of
cycles: a configuration that passes `checkReducibleNum n` is C-reducible. -/
theorem check_reducible_valid_num {n : ℕ} {cf : Config}
    (hchk : checkReducibleNum n cf = true) : CfReducible cf := by
  rw [checkReducibleNum] at hchk
  exact check_reducible_valid_of_coclosure hchk fun et hlen hmem =>
    kempeCoclosure_of_not_mem_kempeTreeNum cf.prog hlen hmem

/-! ### Reducibility over a range of configurations

The predicate that hides the (expensive) reducibility evaluation, together with
the two lemmas the reducibility job files use: one to discharge a range by
evaluating the check at each index, and one to glue contiguous ranges. -/

/-- The reference's `cf000`: an arbitrary configuration, used as the default
value when indexing outside a list of configurations. -/
def cf000 : Config := ⟨false, [0], [.H]⟩

/-- `cf000` is the default configuration, so that `cfs[i]!` is available. -/
instance : Inhabited Config := ⟨cf000⟩

/-- All configurations in the range `[j₁, j₂)` of `cfs` are C-reducible. -/
def ReducibleInRange (j₁ j₂ : ℕ) (cfs : List Config) : Prop :=
  ∀ i, j₁ ≤ i → i < j₂ → CfReducible cfs[i]!

/-- Indexing into a slice of a list. -/
private theorem getElem!_take_drop (cfs : List Config) (j n m : ℕ) (hm : m < n) :
    ((cfs.drop j).take n)[m]! = cfs[j + m]! := by
  simp only [List.getElem!_eq_getElem?_getD]
  congr 1
  rw [List.getElem?_take_of_lt hm, List.getElem?_drop]

/-- **A single configuration, checked by the iterated test.**  This is the
granularity the reducibility job files use: the Lean kernel retains every
reduction it performs for the lifetime of a module, so one configuration per
module is what keeps the peak memory to the cost of a single check. -/
theorem reducible_range_one_num {n i : ℕ} {cfs : List Config}
    (h : checkReducibleNum n cfs[i]! = true) : ReducibleInRange i (i + 1) cfs := by
  intro j hj hj'
  have hji : j = i := by omega
  subst hji
  exact check_reducible_valid_num h

/-- One reducible configuration is a reducible range of length one. -/
theorem reducible_range_one {i : ℕ} {cfs : List Config} (h : CfReducible cfs[i]!) :
    ReducibleInRange i (i + 1) cfs := by
  intro j hj hj'
  have hji : j = i := by omega
  subst hji
  exact h

/-- **Checking a range of configurations by evaluation.**  The hypothesis is
kept in the reference's shape, a disjunction over a single index, so that a job
file can discharge it case by case with `decide +kernel`. -/
theorem check_reducible_in_range {j₁ j₂ : ℕ} {cfs : List Config}
    (h : ∀ i, j₂ - j₁ ≤ i ∨
      checkReducible ((cfs.drop j₁).take (j₂ - j₁))[i]! = true) :
    ReducibleInRange j₁ j₂ cfs := by
  intro i hi hij
  have hlt : i - j₁ < j₂ - j₁ := by omega
  rcases h (i - j₁) with hge | hchk
  · omega
  · rw [getElem!_take_drop cfs j₁ _ _ hlt, show j₁ + (i - j₁) = i by omega] at hchk
    exact check_reducible_valid hchk

/-- **Checking a range of configurations by evaluation at a chosen depth**, the
counterpart of `check_reducible_in_range` for `checkReducibleAt`.  The depth is
uniform over the range, so a job file gives each configuration its own depth by
splitting the range and gluing the pieces with `cat_reducible_range`. -/
theorem check_reducible_in_range_at {d j₁ j₂ : ℕ} {cfs : List Config}
    (h : ∀ i, j₂ - j₁ ≤ i ∨
      checkReducibleAt d ((cfs.drop j₁).take (j₂ - j₁))[i]! = true) :
    ReducibleInRange j₁ j₂ cfs := by
  intro i hi hij
  have hlt : i - j₁ < j₂ - j₁ := by omega
  rcases h (i - j₁) with hge | hchk
  · omega
  · rw [getElem!_take_drop cfs j₁ _ _ hlt, show j₁ + (i - j₁) = i by omega] at hchk
    exact check_reducible_valid_at hchk

/-- Two contiguous reducible ranges combine into one. -/
theorem cat_reducible_range {j₁ j₂ : ℕ} {cfs : List Config}
    (h₁₂ : ReducibleInRange j₁ j₂ cfs) {j₃ : ℕ} (h₂₃ : ReducibleInRange j₂ j₃ cfs) :
    ReducibleInRange j₁ j₃ cfs := by
  intro i hi hij
  rcases Nat.lt_or_ge i j₂ with hlt | hge
  · exact h₁₂ i hi hlt
  · exact h₂₃ i hge hij

end FourColor


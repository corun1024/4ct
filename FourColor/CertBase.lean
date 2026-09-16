import FourColor.CfReducible

/-!
# Kempe co-closure by certificate: the semantic core

`FourColor.CfReducible` decides C-reducibility by computing the Kempe closure
tree — the *greatest* Kempe-closed set of traces disjoint from the colourings of
the configuration — as a global fixpoint over the whole trace space.  The check
only ever asks that the (few) contract traces lie *outside* that set, and being
outside it is a *least*-fixpoint statement, with short local derivations:

* **(G)** a ring trace is in the co-closure;
* **(P)** the co-closure is stable under colour permutations;
* **(K)** if every chromogram matching `et` has some matching trace already
  known to be in the co-closure, then so is `et`.

Rule (K) with its descent order is `kempeCoclosure_of_rank` of
`FourColor.Chromogram`.  This file proves (P), rule (G) in the form the checker
uses, and the bridge from "every contract trace is in the co-closure" to
`CfReducible`.  Nothing here computes:
the decidable certificate checker is built on top in `FourColor.Cert`.

## Main results

* `kempeCoclosure_of_map` — rule (P).
* `ringTrace_rot_of_mem_cpcolor` — rule (G), in the form the checker uses.
* `cfReducible_of_coclosure` — the bridge: a configuration whose contract traces
  all lie in the Kempe co-closure is C-reducible.
-/

namespace FourColor

open Color

/-! ### Rule (P): the co-closure is stable under colour permutations -/

/-- **Rule (P).**  A Kempe-closed predicate is stable under colour
permutations, so a trace whose image under some permutation is in the
co-closure is itself in the co-closure. -/
theorem kempeCoclosure_of_map {P : List Color → Prop} {et : List Color} (g : EdgePerm)
    (h : KempeCoclosure P (et.map g)) : KempeCoclosure P et := by
  intro P₁ hP₁ hP₁et
  exact h P₁ hP₁ ((hP₁ et hP₁et).1 g)

/-! ### Rule (G): membership in the colouring tree -/

/-- Moving the head of a list to its back is the one-step rotation. -/
private theorem rotate_one_cons {α : Type*} (a : α) (l : List α) :
    (a :: l).rotate 1 = l ++ [a] := by
  rw [List.rotate_cons_succ, List.rotate_zero]

/-- **Rule (G).**  A trace held by the colouring tree of a construction program
completes to a ring trace of the once-rotated ring — which is the predicate the
Kempe co-closure of `FourColor.CfReducible` is taken with respect to. -/
theorem ringTrace_rot_of_mem_cpcolor {cp : CProg} {e : List Color}
    (he : Ctree.mem (cpcolor cp) e = true) :
    (cpmap cp).map.RingTrace ((cpmap cp).cpring.rotate 1) (completeTrace e) := by
  obtain ⟨-, k, hk, hDet⟩ := (ctree_mem_cpcolor cp e).mp he
  refine ⟨k, hk, ?_⟩
  rw [List.map_rotate, trace_rotate, ← hDet, rotate_one_cons, completeTrace]

/-! ### The bridge to `CfReducible` -/

/-- A nonempty trace that sums to zero is the rotation of the completion of its
tail. -/
private theorem rotate_one_eq_completeTrace {et : List Color} (hne : et ≠ [])
    (hsum : et.sum = 0) : et.rotate 1 = completeTrace et.tail := by
  cases et with
  | nil => exact absurd rfl hne
  | cons e t =>
    rw [List.sum_cons] at hsum
    rw [rotate_one_cons, List.tail_cons, completeTrace, Color.add_eq_zero_iff.mp hsum]

/-- Rotating a predicate on traces by one step, backwards. -/
private def rotatedBack (P : List Color → Prop) (et : List Color) : Prop :=
  ∃ es, es.rotate 1 = et ∧ P es

/-- Kempe closure is stable under rotating the predicate. -/
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

/-- Transporting a Kempe co-closure of ring traces along a rotation of the
ring. -/
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

/-- **The bridge.**  A configuration with a well-formed contract, every trace of
whose contract tree completes to a member of the Kempe co-closure of the ring
traces, is C-reducible.

This is the shape of `check_reducible_valid_of_coclosure` of
`FourColor.CfReducible` that a certificate discharges: instead of a tree
disjoint from the contract tree, the hypothesis speaks directly about the
traces the contract tree holds. -/
theorem cfReducible_of_coclosure {cf : Config} {cct : Ctree}
    (hc : contractCtree cf = some cct)
    (hco : ∀ es : List Color, Ctree.mem cct (evenize es) = true →
      KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1))
        (completeTrace es)) :
    CfReducible cf := by
  obtain ⟨hvalid, hcol⟩ := contract_ctreeP hc
  refine ⟨hvalid, ?_⟩
  intro et htr
  have hsize : (cfmap cf).cpring.length = cprsize cf.prog := size_ring_cpmap cf.prog
  have hrr : (cfring cf).reverse = (cfmap cf).cpring := List.reverse_reverse _
  have hmem := hcol et htr
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
  have hcot : KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1))
      (et.rotate 1) := by
    rw [rotate_one_eq_completeTrace hne hsum]
    exact hco et.tail hmem
  rw [hrr]
  exact kempeCoclosure_of_rotate hcot

end FourColor

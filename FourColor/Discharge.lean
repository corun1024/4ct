import Mathlib.Tactic.Linarith
import FourColor.Orbit
import FourColor.Part

/-!
# Discharging: moving charge between the faces of a pentagonal map

Robertson, Sanders, Seymour and Thomas prove the unavoidability half of the
Four Colour Theorem by a *discharging* argument: every face `F` of a plain
cubic pentagonal map starts with the charge `10 * (6 - #F)`, and thirty-two
*rules* move one unit of charge at a time from a face to a neighbour.  Euler's
formula says that the total charge is `120`, so some face ends up positively
charged, and the local configuration around such a face is then shown to be
reducible.

Each rule is a `Part`: it describes the second neighbourhood of a dart, and
whenever it fits at a dart `x` one unit of charge moves from the face of `x` to
the face of `edge (face^2 x)`.  The two-face shift is what makes the converse
of a rule expressible as a part again.

## Main definitions

* `drule1`, …, `drule32` — the part encodings of the thirty-two rules, with the
  primed variants that specialise a rule by hub arity or by symmetry.
* `baseDrules` — the thirty-eight rules with multiplicity, and
  `symmetrizeDrules`, `theDrules` — the rules completed with their mirror
  images across the third spoke.
* `Hypermap.invFace2` — `face⁻²`, the dart whose second neighbourhood a rule
  is tested against.
* `Hypermap.dscore1`, `Hypermap.dscore2`, `Hypermap.dscore` — the charge
  transferred across a dart, the net transfer across an edge, and the total
  charge of a face.
* `pickSourceDrules`, `pickTargetDrules`, `DruleFork` — the rules specialised
  to a given hub arity, and `sortDrules`, `SortDrulesResult` — the rules
  sorted against a part, used to bound scores during the enumeration of parts.
* `Hypermap.dbound1`, `Hypermap.dbound2`, `dboundK` — the bounds themselves.

## Main results

* `Hypermap.dscore_cface` — the charge only depends on the face.
* `Hypermap.sum_dscore_transversal` — the total charge of a planar plain cubic
  connected map is `120`; this is Euler's formula in disguise.
* `Hypermap.posz_dscore` — some dart of such a map is positively charged.
* `Hypermap.dbound1_eq`, `Hypermap.dbound2_le`, `Hypermap.dboundK_eq`,
  `Hypermap.sort_dbound1_eq` — the bounds are correct.
* `Hypermap.dscore_cap1`, `Hypermap.dscore_cap2` — the two consequences of a
  positive charge that the unavoidability computation uses.

## Implementation notes

`Hypermap.arity` is noncomputable, so the fitting predicates are `Prop`-valued
and not decidable; the counts `dscore1` and `dbound1` are therefore
`List.countP` of a classically decided predicate and are noncomputable.

The reference states the total charge as a sum over the canonical roots of the
face orbits.  Here it is stated for an arbitrary *transversal* of the faces, a
list `r` that is face-simple (`Hypermap.Simple`) and meets every face
(`Hypermap.Fband`); `Hypermap.exists_face_transversal` produces one.

`converse_part` and `fitp_converse` are not part of the `Part` port, so the
target rules of a `DruleFork` and the bound `dbound2_le` take the converse
operation and its correctness as parameters.  For the same reason
`dscore_mirror` is not ported: it rests on `fitp_mirror`.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file
corresponds to `theories/proof/discharge.v` of the Coq development.
-/

namespace FourColor

open Equiv Equiv.Perm

/-! ### The discharge rules

Each rule is read counterclockwise from the hub dart: `$ s` is a spoke of
arity range `s` with an unconstrained hat, `$[h] s` constrains the hat too, and
`$[h f1 …] n` describes a spoke of arity exactly `n` together with its fans. -/

section Rules

open FourColor.Part FourColor.PRange

/-- Discharge rule `drule1`, written `$ * $ * $ 6+ $ * $ * $` in the reference. -/
def drule1 : Part :=
  cons pr59 pr59 <| cons pr59 pr59 <| cons pr69 pr59 <| cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule2`, written `$ * $ 5 $ 7+ $ * $ * $` in the reference. -/
def drule2 : Part :=
  cons pr59 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <| cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule2'`, written `$ * $ 5 $ 7+ $ * $ * $ * $` in the reference. -/
def drule2' : Part :=
  cons pr59 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 nil

/-- Discharge rule `drule3`, written `$ 5 $ 6- $ 6+ $ * $ * $` in the reference. -/
def drule3 : Part :=
  cons pr55 pr59 <| cons pr56 pr59 <| cons pr69 pr59 <| cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule3'`, written `$ 5 $ 6- $ 6+ $ * $ * $ * $` in the reference. -/
def drule3' : Part :=
  cons pr55 pr59 <| cons pr56 pr59 <| cons pr69 pr59 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 nil

/-- Discharge rule `drule4`, written `$ 6- $[5] 5 $ 6+ $ * $ * $ * $` in the reference. -/
def drule4 : Part :=
  cons pr56 pr59 <| cons pr55 pr55 <| cons pr69 pr59 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 nil

/-- Discharge rule `drule4'`, written `$ 6- $[5] 6 $ 6+ $ * $ * $ * $` in the reference. -/
def drule4' : Part :=
  cons pr56 pr59 <| cons pr66 pr55 <| cons pr69 pr59 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 nil

/-- Discharge rule `drule5`, written `$ 6 $[6- 5] 6 $ 6+ $ * $ * $ * $` in the reference. -/
def drule5 : Part :=
  cons pr66 pr59 <| cons6 pr56 pr55 <| cons pr69 pr59 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 nil

/-- Discharge rule `drule6`, written `$ 6 $[6-] 5 $[5] 7+ $ * $ * $ * $` in the reference. -/
def drule6 : Part :=
  cons pr66 pr59 <| cons pr55 pr56 <| cons pr79 pr55 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 nil

/-- Discharge rule `drule7`, written `$ 6 $[6 6-] 6 $[5] 7+ $ * $ * $ * $` in the reference. -/
def drule7 : Part :=
  cons pr66 pr59 <| cons6 pr66 pr56 <| cons pr79 pr55 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 nil

/-- Discharge rule `drule8`, written `$ 5 $ 6- $ 7+ $ * $ * $ * $ * $` in the reference. -/
def drule8 : Part :=
  cons pr55 pr59 <| cons pr56 pr59 <| cons pr79 pr59 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule9`, written `$ 6- $ 6- $ 7+ $ * $ * $ * $ 5 $` in the reference. -/
def drule9 : Part :=
  cons pr56 pr59 <| cons pr56 pr59 <| cons pr79 pr59 <| cons pr59 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule10`, written `$ 5 $ 5 $ 7+ $ 5 $ 6+ $ * $ * $` in the reference. -/
def drule10 : Part :=
  cons pr55 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr69 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule10'`, written `$ 5 $ 5 $ 7+ $ 5 $ 5 $ * $ * $` in the reference. -/
def drule10' : Part :=
  cons pr55 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr55 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule11`, written `$ 6 $[5] 5 $ 7+ $ 5 $ 6+ $ * $ * $` in the reference. -/
def drule11 : Part :=
  cons pr66 pr59 <| cons pr55 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr69 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule12`, written `$ 5 $[5] 5 $ 7+ $ 5 $[5] 5 $ * $ * $` in the reference. -/
def drule12 : Part :=
  cons pr55 pr59 <| cons pr55 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr55 pr55 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule13`, written `$ 6 $[5] 5 $[5] 8+ $ 5 $ 5 $ * $ * $` in the reference. -/
def drule13 : Part :=
  cons pr66 pr59 <| cons pr55 pr55 <| cons pr89 pr55 <| cons pr55 pr59 <| cons pr55 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule14`, written `$ 5 $[5] 6 $ 7+ $ 5 $ * $ * $ * $` in the reference. -/
def drule14 : Part :=
  cons pr55 pr59 <| cons pr66 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule15`, written `$ 5 $ 6 $ 7+ $ 5 $ 7+ $ 5 $ 6 $` in the reference. -/
def drule15 : Part :=
  cons pr55 pr59 <| cons pr66 pr59 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <|
    cons pr55 pr59 <| cons pr66 pr59 nil

/-- Discharge rule `drule16`, written `$ 6 $ 6 $ 7+ $ 5 $ 5 $ 5 $ 6 $` in the reference. -/
def drule16 : Part :=
  cons pr66 pr59 <| cons pr66 pr59 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr55 pr59 <|
    cons pr55 pr59 <| cons pr66 pr59 nil

/-- Discharge rule `drule17`, written `$ 5 $[6] 6 $ 7+ $ 5 $ 5 $ 7+ $ 5 $` in the reference. -/
def drule17 : Part :=
  cons pr55 pr59 <| cons pr66 pr66 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr55 pr59 <|
    cons pr79 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule18`, written `$ 6 $[5] 5 $[5] 7 $ 6+ $ * $ * $ 5 $` in the reference. -/
def drule18 : Part :=
  cons pr66 pr59 <| cons pr55 pr55 <| cons pr77 pr55 <| cons pr69 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule19`, written `$ 6 $ 6+ $ 8+ $[5] 5 $[5] 6 $ 5 $ 6 $` in the reference. -/
def drule19 : Part :=
  cons pr66 pr59 <| cons pr69 pr59 <| cons pr89 pr59 <| cons pr55 pr55 <| cons pr66 pr55 <|
    cons pr55 pr59 <| cons pr66 pr59 nil

/-- Discharge rule `drule20`, written `$ 5 $ 6 $ 7+ $ 6 $ 6 $ 5 $ 5 $` in the reference. -/
def drule20 : Part :=
  cons pr55 pr59 <| cons pr66 pr59 <| cons pr79 pr59 <| cons pr66 pr59 <| cons pr66 pr59 <|
    cons pr55 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule21`, written `$ 6- $ 6 $[5] 7 $ 6+ $ * $ 5 $ 5 $` in the reference. -/
def drule21 : Part :=
  cons pr56 pr59 <| cons pr66 pr59 <| cons pr77 pr55 <| cons pr69 pr59 <| cons pr59 pr59 <|
    cons pr55 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule22`, written `$ 5 $ 6 $[5] 7 $ 6+ $ * $ 5 $ 6 $` in the reference. -/
def drule22 : Part :=
  cons pr55 pr59 <| cons pr66 pr59 <| cons pr77 pr55 <| cons pr69 pr59 <| cons pr59 pr59 <|
    cons pr55 pr59 <| cons pr66 pr59 nil

/-- Discharge rule `drule23`, written `$ 5 $[5] 7 $ 7+ $ 5 $ * $ * $ * $` in the reference. -/
def drule23 : Part :=
  cons pr55 pr59 <| cons pr77 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule24`, written `$ 5 $ 5 $[5] 7 $ 7+ $ 6 $ 6 $ 5 $` in the reference. -/
def drule24 : Part :=
  cons pr55 pr59 <| cons pr55 pr59 <| cons pr77 pr55 <| cons pr79 pr59 <| cons pr66 pr59 <|
    cons pr66 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule25`, written
`$ 5 $ 5 $ 7+ $[* * 5] 7 $[6] 5 $ 5 $ * $` in the reference. -/
def drule25 : Part :=
  cons pr55 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <| cons7 pr59 pr59 pr55 <| cons pr55 pr66 <|
    cons pr55 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule26`, written `$ 6 $ 6 $[5] 7 $ 7+ $ 5 $ 5 $ 6 $` in the reference. -/
def drule26 : Part :=
  cons pr66 pr59 <| cons pr66 pr59 <| cons pr77 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <|
    cons pr55 pr59 <| cons pr66 pr59 nil

/-- Discharge rule `drule27`, written
`$ 7+ $ 6 $[6 5 6+] 7 $ 7 $[5] 6- $ * $ * $` in the reference. -/
def drule27 : Part :=
  cons pr79 pr59 <| cons pr66 pr59 <| cons7 pr66 pr55 pr69 <| cons pr77 pr59 <| cons pr56 pr55 <|
    cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule28`, written `$ 5 $ 5 $ 7+ $ 5 $ 5 $ * $ * $ 5 $` in the reference. -/
def drule28 : Part :=
  cons pr55 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr55 pr59 <|
    cons pr59 pr59 <| cons pr59 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule29`, written `$ 5 $[5] 5 $ 7+ $ 5 $ * $ * $ 5 $ 5 $` in the reference. -/
def drule29 : Part :=
  cons pr55 pr59 <| cons pr55 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr59 pr59 <|
    cons pr59 pr59 <| cons pr55 pr59 <| cons pr55 pr59 nil

/-- Discharge rule `drule30`, written `$ 5 $ 5 $ 7+ $ 5 $[5] 6 $ 5 $ * $ * $` in the reference. -/
def drule30 : Part :=
  cons pr55 pr59 <| cons pr55 pr59 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr66 pr55 <|
    cons pr55 pr59 <| cons pr59 pr59 <| cons pr59 pr59 nil

/-- Discharge rule `drule31`, written
`$ 5 $[5] 5 $ 7+ $ 5 $[6+] 5 $ 6+ $ * $ 6+ $` in the reference. -/
def drule31 : Part :=
  cons pr55 pr59 <| cons pr55 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr55 pr69 <|
    cons pr69 pr59 <| cons pr59 pr59 <| cons pr69 pr59 nil

/-- Discharge rule `drule31'`, written
`$ 5 $[5] 5 $ 7+ $ 5 $[5] 5 $ 6+ $ * $ 6+ $` in the reference. -/
def drule31' : Part :=
  cons pr55 pr59 <| cons pr55 pr55 <| cons pr79 pr59 <| cons pr55 pr59 <| cons pr55 pr55 <|
    cons pr69 pr59 <| cons pr59 pr59 <| cons pr69 pr59 nil

/-- Discharge rule `drule32`, written `$ 5 $ 6 $[5] 7 $ 7+ $ 6 $ 5 $ 5 $ 5 $` in the reference. -/
def drule32 : Part :=
  cons pr55 pr59 <| cons pr66 pr59 <| cons pr77 pr55 <| cons pr79 pr59 <| cons pr66 pr59 <|
    cons pr55 pr59 <| cons pr55 pr59 <| cons pr55 pr59 nil

end Rules

/-- The discharge rules, with multiplicity: `drule1` occurs twice because it
transfers two units of charge, and the primed rules specialise `drule2`,
`drule3`, `drule4`, `drule10` and `drule31` by hub arity or by symmetry. -/
def baseDrules : List Part :=
  [drule1, drule1, drule2, drule2', drule3, drule3', drule4, drule4', drule5,
    drule6, drule7, drule8, drule9, drule10, drule10',
    drule11, drule12, drule13, drule14, drule15, drule16, drule17, drule18, drule19,
    drule20, drule21, drule22, drule23, drule24, drule25, drule26, drule27, drule28, drule29,
    drule30, drule31, drule31', drule32]

/-- The reflection of a rule across its third spoke: mirror the part, then turn
it back by five subparts. -/
def reflectDrule (p : Part) : Part := (fun q => q.rot (p.size - 1))^[5] p.mirror

/-- Complete a list of rules by adding the reflection across the third spoke of
every rule that is not already symmetric. -/
def symmetrizeDrules : List Part → List Part
  | [] => []
  | p :: rs =>
      if p.cmp (reflectDrule p) = .subset then p :: symmetrizeDrules rs
      else reflectDrule p :: p :: symmetrizeDrules rs

/-- The discharge rules actually used to adjust the charges: each part that
fits at a dart `x` moves one unit of charge from the face of `x` to the face of
`edge (face^2 x)`. -/
def theDrules : List Part := symmetrizeDrules baseDrules

/-! ### Counting the rules that fit

`Hypermap.arity` is noncomputable, so the fitting predicates are `Prop`-valued
and undecidable; the counts below are therefore taken classically. -/

/-- The number of parts of `rs` that satisfy `P`, counted with multiplicity. -/
noncomputable def dcount (P : Part → Prop) (rs : List Part) : ℕ :=
  rs.countP fun p => @decide _ (Classical.propDecidable (P p))

@[simp] theorem dcount_nil (P : Part → Prop) : dcount P [] = 0 := rfl

/-- Counting through a cons whose head satisfies the predicate. -/
theorem dcount_cons_pos {P : Part → Prop} {p : Part} (hp : P p) (rs : List Part) :
    dcount P (p :: rs) = dcount P rs + 1 := by
  have h : (@decide _ (Classical.propDecidable (P p))) = true := by simpa using hp
  simp [dcount, h]

/-- Counting through a cons whose head fails the predicate. -/
theorem dcount_cons_neg {P : Part → Prop} {p : Part} (hp : ¬ P p) (rs : List Part) :
    dcount P (p :: rs) = dcount P rs := by
  have h : (@decide _ (Classical.propDecidable (P p))) = false := by simpa using hp
  simp [dcount, h]

/-- Two pointwise equivalent predicates have the same count. -/
theorem dcount_congr {P Q : Part → Prop} (h : ∀ p, P p ↔ Q p) (rs : List Part) :
    dcount P rs = dcount Q rs := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    by_cases hp : P p
    · rw [dcount_cons_pos hp, dcount_cons_pos ((h p).mp hp), ih]
    · rw [dcount_cons_neg hp, dcount_cons_neg (fun hq => hp ((h p).mpr hq)), ih]

/-- A count only gets bigger when the predicate gets weaker. -/
theorem dcount_mono {P Q : Part → Prop} {rs : List Part} (h : ∀ p ∈ rs, P p → Q p) :
    dcount P rs ≤ dcount Q rs := by
  induction rs with
  | nil => exact le_rfl
  | cons p rs ih =>
    have hrs := ih fun q hq => h q (List.mem_cons_of_mem p hq)
    by_cases hp : P p
    · rw [dcount_cons_pos hp, dcount_cons_pos (h p (List.mem_cons_self) hp)]
      omega
    · rw [dcount_cons_neg hp]
      by_cases hq : Q p
      · rw [dcount_cons_pos hq]; omega
      · rw [dcount_cons_neg hq]; omega

/-- The count of a conjunction whose first half is a decision procedure is the
count of the second half over the filtered list. -/
theorem dcount_filter (q : Part → Bool) (P : Part → Prop) (rs : List Part) :
    dcount (fun p => q p = true ∧ P p) rs = dcount P (rs.filter q) := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    by_cases hq : q p = true
    · rw [List.filter_cons_of_pos hq]
      by_cases hp : P p
      · rw [dcount_cons_pos (show q p = true ∧ P p from ⟨hq, hp⟩), dcount_cons_pos hp, ih]
      · rw [dcount_cons_neg (show ¬ (q p = true ∧ P p) from fun h => hp h.2),
          dcount_cons_neg hp, ih]
    · rw [List.filter_cons_of_neg hq,
        dcount_cons_neg (show ¬ (q p = true ∧ P p) from fun h => hq h.1), ih]

/-- A count grows when a part is prepended to the list. -/
theorem dcount_le_cons (P : Part → Prop) (p : Part) (rs : List Part) :
    dcount P rs ≤ dcount P (p :: rs) := by
  by_cases hp : P p
  · rw [dcount_cons_pos hp]; omega
  · rw [dcount_cons_neg hp]

/-! ### List helpers for the sums over a face -/

/-- The sum of a flattened list of lists. -/
private theorem sum_flatten (L : List (List ℤ)) : L.flatten.sum = (L.map List.sum).sum := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

/-- A pointwise bound on a sum over a list. -/
private theorem sum_map_le {α : Type*} {l : List α} {f g : α → ℤ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem a hb))

/-- A uniform bound on a sum over a list. -/
private theorem sum_map_le_const {α : Type*} {l : List α} {f : α → ℤ} {c : ℤ}
    (h : ∀ a ∈ l, f a ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul]
    linarith

namespace Hypermap

variable {D : Type*} (G : Hypermap D)

/-! ### The dart two faces back

`Hypermap.invFace2` itself is defined in `FourColor.Part`; a discharge rule is
tested at `invFace2 x` to decide whether charge crosses the edge at `x`. -/

@[simp] theorem invFace2_face_face (x : D) : G.invFace2 (G.face (G.face x)) = x := by
  simp [invFace2]

@[simp] theorem face_face_invFace2 (x : D) : G.face (G.face (G.invFace2 x)) = x := by
  simp [invFace2]

/-! ### Charges -/

variable [Finite D]

/-- The charge transferred from the face of `x` to the face of `edge x`: the
number of discharge rules that fit exactly at `invFace2 x`. -/
noncomputable def dscore1 (x : D) : ℕ := dcount (G.ExactFitp (G.invFace2 x)) theDrules

/-- The net charge transferred into the face of `x` across the edge at `x`. -/
noncomputable def dscore2 (x : D) : ℤ := (G.dscore1 (G.edge x) : ℤ) - G.dscore1 x

/-- The charge of the face of `x`: the initial charge `10 * (6 - #F)` of that
face, plus the adjustments the discharge rules make at each of its darts. -/
noncomputable def dscore (x : D) : ℤ :=
  60 - 10 * (G.arity x : ℤ) + ((orbitList G.face x).map G.dscore2).sum

/-- Darts on the same face have the same orbit list, up to rotation. -/
theorem perm_orbitList {x y : D} (h : G.CFace x y) :
    (orbitList G.face x).Perm (orbitList G.face y) :=
  (List.perm_ext_iff_of_nodup (nodup_orbitList _ _) (nodup_orbitList _ _)).mpr fun _ => by
    simp only [mem_orbitList]
    exact ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

/-- The charge is a property of the face, not of the dart. -/
theorem dscore_cface {x y : D} (h : G.CFace x y) : G.dscore x = G.dscore y := by
  rw [dscore, dscore, G.arity_cface h, ((G.perm_orbitList h).map G.dscore2).sum_eq]

/-- Turning around a face permutes its orbit list. -/
theorem perm_map_face (x : D) :
    ((orbitList G.face x).map G.face).Perm (orbitList G.face x) := by
  refine (List.perm_ext_iff_of_nodup ((nodup_orbitList G.face x).map G.face.injective)
    (nodup_orbitList G.face x)).mpr fun a => ?_
  simp only [List.mem_map, mem_orbitList]
  refine ⟨?_, fun ha => ⟨G.face.symm a, ?_, Equiv.apply_symm_apply _ _⟩⟩
  · rintro ⟨b, hb, rfl⟩
    exact sameCycle_apply_right.mpr hb
  · exact sameCycle_apply_right.mp (by rwa [Equiv.apply_symm_apply])

/-- A sum over a face is unchanged by shifting the darts two faces on. -/
theorem sum_map_face_face (x : D) (f : D → ℤ) :
    ((orbitList G.face x).map fun y => f (G.face (G.face y))).sum
      = ((orbitList G.face x).map f).sum :=
  calc ((orbitList G.face x).map fun y => f (G.face (G.face y))).sum
      = (((orbitList G.face x).map G.face).map fun y => f (G.face y)).sum := by
        rw [List.map_map]; rfl
    _ = ((orbitList G.face x).map fun y => f (G.face y)).sum :=
        ((G.perm_map_face x).map _).sum_eq
    _ = (((orbitList G.face x).map G.face).map f).sum := by rw [List.map_map]; rfl
    _ = ((orbitList G.face x).map f).sum := ((G.perm_map_face x).map f).sum_eq

/-! ### The total charge of a planar map

The reference sums the charges over the canonical roots of the face orbits.
Here the sum is taken over an arbitrary *transversal* of the faces: a list that
is face-simple and meets every face. -/

section Planar

omit [Finite D] in
/-- The face orbit of a dart has the arity of that dart as its length. -/
@[simp] theorem length_orbitList_face (x : D) : (orbitList G.face x).length = G.arity x :=
  length_orbitList _ _

omit [Finite D] in
/-- The charges of a list of darts, split into the initial charges and the
adjustments made along the faces of those darts. -/
private theorem sum_map_dscore (l : List D) :
    (l.map G.dscore).sum
      = 60 * (l.length : ℤ) - 10 * (((l.map fun x => orbitList G.face x).flatten).length : ℤ)
        + (((l.map fun x => orbitList G.face x).flatten).map G.dscore2).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, dscore, List.flatten_cons, List.length_append,
      List.map_append, List.sum_append, List.length_cons, length_orbitList_face]
    push_cast
    ring

/-- Every finite hypermap has a transversal of its faces. -/
theorem exists_face_transversal : ∃ r : List D, G.Simple r ∧ ∀ x : D, G.Fband r x := by
  classical
  have : Fintype (Quotient (SameCycle.setoid G.face)) := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset (Quotient (SameCycle.setoid G.face))).toList.map Quotient.out,
    ?_, fun x => ?_⟩
  · rw [G.simple_iff_nodup_map, List.map_map]
    simpa [Function.comp_def, Quotient.out_eq] using Finset.nodup_toList
      (Finset.univ : Finset (Quotient (SameCycle.setoid G.face)))
  · refine ⟨(Quotient.mk (SameCycle.setoid G.face) x).out, ?_, ?_⟩
    · exact List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ _))
    · have h := Quotient.exact (Quotient.out_eq (Quotient.mk (SameCycle.setoid G.face) x))
      exact (h : G.face.SameCycle _ _).symm

/-- **The total charge is 120**: the sum of the charges of the faces of a
planar plain cubic connected hypermap, which is Euler's formula in disguise. -/
theorem sum_dscore_transversal (hG : G.PlanarPlainCubicConnected) {r : List D}
    (hs : G.Simple r) (hc : ∀ x : D, G.Fband r x) : (r.map G.dscore).sum = 120 := by
  classical
  have : Fintype D := Fintype.ofFinite D
  set L : List D := (r.map fun x => orbitList G.face x).flatten with hLdef
  have hnodup : L.Nodup := by
    rw [hLdef, List.nodup_flatten]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hl
      exact nodup_orbitList _ _
    · have hs' : r.Pairwise fun x y => ¬ G.CFace x y := hs
      have hdisj : ∀ {a b : D}, ¬ G.CFace a b →
          (orbitList G.face a).Disjoint (orbitList G.face b) := by
        intro a b hab c hc1 hc2
        exact hab ((mem_orbitList.mp hc1).trans (mem_orbitList.mp hc2).symm)
      rw [List.pairwise_map]
      exact hs'.imp hdisj
  have hmem : ∀ x : D, x ∈ L := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hc x
    exact List.mem_flatten.mpr ⟨orbitList G.face y, List.mem_map_of_mem hy,
      mem_orbitList.mpr hxy.symm⟩
  have htf : L.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun x => List.mem_toFinset.mpr (hmem x)
  have hlen : L.length = Nat.card D := by
    rw [← List.toFinset_card_of_nodup hnodup, htf, Finset.card_univ, Nat.card_eq_fintype_card]
  have hsum2 : (L.map G.dscore2).sum = 0 := by
    have hz : ∑ x : D, G.dscore2 x = 0 := by
      simp only [dscore2, Finset.sum_sub_distrib,
        Equiv.sum_comp G.edge fun y => (G.dscore1 y : ℤ), sub_self]
    rw [← List.sum_toFinset _ hnodup, htf]
    exact hz
  have hrlen : r.length = cycleCount G.face := by
    have : Fintype (Quotient (SameCycle.setoid G.face)) := Fintype.ofFinite _
    have hq : (r.map (Quotient.mk (SameCycle.setoid G.face))).Nodup :=
      G.simple_iff_nodup_map.mp hs
    have hall : ∀ c : Quotient (SameCycle.setoid G.face),
        c ∈ r.map (Quotient.mk (SameCycle.setoid G.face)) := by
      intro c
      obtain ⟨x, rfl⟩ := Quotient.exists_rep c
      obtain ⟨y, hy, hxy⟩ := hc x
      exact List.mem_map.mpr ⟨y, hy, Quotient.sound hxy.symm⟩
    have : (r.map (Quotient.mk (SameCycle.setoid G.face))).length
        = Nat.card (Quotient (SameCycle.setoid G.face)) := by
      rw [← List.toFinset_card_of_nodup hq,
        Finset.eq_univ_of_forall fun c => List.mem_toFinset.mpr (hall c), Finset.card_univ,
        Nat.card_eq_fintype_card]
    simpa [cycleCount] using this
  have heuler : 6 * cycleCount G.face = Nat.card D + 12 :=
    (cubic_Euler hG.base.base.plain hG.base.base.cubic hG.base.connected).mp hG.planar
  rw [G.sum_map_dscore r, ← hLdef, hlen, hrlen, hsum2]
  omega

/-- **Some face is positively charged** in a planar plain cubic connected
hypermap. -/
theorem posz_dscore (hG : G.PlanarPlainCubicConnected) : ∃ x : D, 0 < G.dscore x := by
  refine Classical.byContradiction fun h => ?_
  have h' : ∀ x : D, G.dscore x ≤ 0 := fun x => not_lt.mp fun hx => h ⟨x, hx⟩
  obtain ⟨r, hs, hc⟩ := G.exists_face_transversal
  have hle : (r.map G.dscore).sum ≤ (r.map fun _ => (0 : ℤ)).sum :=
    sum_map_le fun a _ => h' a
  rw [G.sum_dscore_transversal hG hs hc] at hle
  simp at hle

end Planar

end Hypermap



/-! ### Specialising the rules to a hub arity -/

/-- The rules that take charge away from a hub of arity `n`: those whose part
has exactly `n` subparts. -/
def pickSourceDrules (n : ℕ) (rs : List Part) : List Part :=
  rs.filter fun p => decide (p.size = n)

/-- The converses of the rules that bring charge to a hub of arity `n`.

The reference's `converse_part` is not part of the `Part` port, so the
operation is a parameter `conv` here: `conv p = (u, p')` where `p'` is the
converse part and `u` the range of hub arities it applies to. -/
def pickTargetDrules (conv : Part → PRange × Part) (n : ℕ) : List Part → List Part
  | [] => []
  | p :: rs =>
      let tr := pickTargetDrules conv n rs
      if (conv p).1.Mem n then (conv p).2 :: tr else tr

/-- Selecting a rule whose converse applies to the hub arity. -/
theorem pickTargetDrules_cons_pos {conv : Part → PRange × Part} {n : ℕ} {p : Part}
    (h : (conv p).1.Mem n) (rs : List Part) :
    pickTargetDrules conv n (p :: rs) = (conv p).2 :: pickTargetDrules conv n rs := by
  simp [pickTargetDrules, h]

/-- Discarding a rule whose converse does not apply to the hub arity. -/
theorem pickTargetDrules_cons_neg {conv : Part → PRange × Part} {n : ℕ} {p : Part}
    (h : ¬ (conv p).1.Mem n) (rs : List Part) :
    pickTargetDrules conv n (p :: rs) = pickTargetDrules conv n rs := by
  simp [pickTargetDrules, h]

/-- The discharge rules specialised to a hub of arity `n`: the source and
target rules, together with the witness that they are the ones selected from
`theDrules`.  Computing them once avoids repeating the selection. -/
structure DruleFork (conv : Part → PRange × Part) (n : ℕ) where
  /-- The rules taking charge away from the hub. -/
  source : List Part
  /-- The converses of the rules bringing charge to the hub. -/
  target : List Part
  /-- The source rules are exactly the rules of size `n`. -/
  source_eq : source = pickSourceDrules n theDrules
  /-- The target rules are exactly the converses admitting the hub arity. -/
  target_eq : target = pickTargetDrules conv n theDrules

/-- The discharge rules of a hub arity, computed from `theDrules`. -/
def druleFork (conv : Part → PRange × Part) (n : ℕ) : DruleFork conv n :=
  ⟨pickSourceDrules n theDrules, pickTargetDrules conv n theDrules, rfl, rfl⟩

/-! #### Sorting the rules against a part -/

/-- The rules of a list, sorted against a part: those the part forces are only
counted, those it excludes are dropped, and the rest are kept. -/
structure SortDrulesResult where
  /-- The number of rules of the list that the part forces. -/
  nbForced : ℕ
  /-- The rules that the part neither forces nor excludes. -/
  straddling : List Part

/-- The accumulating recursion behind `sortDrules`. -/
def sortDrulesRec (p : Part) : ℕ → List Part → List Part → SortDrulesResult
  | n, rs, [] => ⟨n, rs⟩
  | n, rs, p' :: r' =>
      match p.cmp p' with
      | .subset => sortDrulesRec p (n + 1) rs r'
      | .straddle => sortDrulesRec p n (p' :: rs) r'
      | .disjoint => sortDrulesRec p n rs r'

/-- Sort the rules `rs` against the part `p`. -/
def sortDrules (p : Part) (rs : List Part) : SortDrulesResult := sortDrulesRec p 0 [] rs

/-- The initial charge of a face of arity `n`, as an integer.

The reference writes this with a truncated subtraction on `ℕ`, which clamps the
value to `10` for `n < 5`; the two agree on the only arities that occur, namely
`n ≥ 5` in a pentagonal map. -/
def dboundK (n : ℕ) : ℤ := 60 - 10 * n

/-! #### The sizes of the discharge rules -/

/-- Reflecting a rule does not change its size. -/
@[simp] theorem size_reflectDrule (p : Part) : (reflectDrule p).size = p.size := by
  simp only [reflectDrule, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, Part.size_rot, Part.size_mirror]

/-- Symmetrising only adds parts of a size already present. -/
theorem exists_size_of_mem_symmetrizeDrules {rs : List Part} {q : Part}
    (hq : q ∈ symmetrizeDrules rs) : ∃ p ∈ rs, q.size = p.size := by
  induction rs with
  | nil => simp [symmetrizeDrules] at hq
  | cons p rs ih =>
    rw [symmetrizeDrules] at hq
    split at hq
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨q, List.mem_cons_self, rfl⟩
      · obtain ⟨p₀, hp₀, hs⟩ := ih hq'
        exact ⟨p₀, List.mem_cons_of_mem _ hp₀, hs⟩
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨p, List.mem_cons_self, size_reflectDrule p⟩
      · rcases List.mem_cons.mp hq' with rfl | hq''
        · exact ⟨q, List.mem_cons_self, rfl⟩
        · obtain ⟨p₀, hp₀, hs⟩ := ih hq''
          exact ⟨p₀, List.mem_cons_of_mem _ hp₀, hs⟩

/-- Every base rule describes a hub of arity between `5` and `8`. -/
theorem size_mem_baseDrules {p : Part} (hp : p ∈ baseDrules) : 5 ≤ p.size ∧ p.size ≤ 8 := by
  have h : baseDrules.all (fun q => 5 ≤ q.size && q.size ≤ 8) = true := by decide
  have := List.all_eq_true.mp h p hp
  simpa using this

/-- Every discharge rule describes a hub of arity between `5` and `8`. -/
theorem size_mem_theDrules {p : Part} (hp : p ∈ theDrules) : 5 ≤ p.size ∧ p.size ≤ 8 := by
  obtain ⟨q, hq, hsz⟩ := exists_size_of_mem_symmetrizeDrules hp
  rw [hsz]
  exact size_mem_baseDrules hq

/-- No rule takes charge from a hub whose arity is outside `[5, 8]`. -/
theorem pickSourceDrules_eq_nil {n : ℕ} (hn : ¬ (5 ≤ n ∧ n ≤ 8)) :
    pickSourceDrules n theDrules = [] := by
  rw [pickSourceDrules, List.filter_eq_nil_iff]
  intro p hp h
  exact hn (by rw [← of_decide_eq_true h]; exact size_mem_theDrules hp)

namespace Hypermap

variable {D : Type*} [Finite D] (G : Hypermap D)

/-! ### Bounds on the charges

The bounds are stated for a hub `x` of a fixed arity `n`; they are what the
enumeration of parts uses to prune its search. -/

/-- The number of parts of `rs` that fit at `x`. -/
noncomputable def dbound1 (rs : List Part) (x : D) : ℕ := dcount (G.Fitp x) rs

/-- The net charge that the rules `rt` bring to, and the rules `rs` take from,
the hub `x`. -/
noncomputable def dbound2 (rt rs : List Part) (x : D) : ℤ :=
  (G.dbound1 rt x : ℤ) - G.dbound1 rs x

omit [Finite D] in
/-- The charge leaving the face of `x` across the edge at `face² x` is the
number of source rules that fit at `x`. -/
theorem dbound1_eq {x : D} {n : ℕ} (hx : G.arity x = n) :
    G.dscore1 (G.face (G.face x)) = G.dbound1 (pickSourceDrules n theDrules) x := by
  rw [dscore1, G.invFace2_face_face, dbound1, pickSourceDrules,
    ← dcount_filter (fun p => decide (p.size = n)) (G.Fitp x) theDrules]
  refine dcount_congr (fun p => ?_) theDrules
  simp only [ExactFitp, hx, decide_eq_true_eq]
  exact and_congr_left' eq_comm

omit [Finite D] in
/-- Counting through a rule that fits. -/
theorem dbound1_cons_pos {x : D} {p : Part} (hp : G.Fitp x p) (rs : List Part) :
    G.dbound1 (p :: rs) x = G.dbound1 rs x + 1 := dcount_cons_pos hp rs

omit [Finite D] in
/-- Counting through a rule that does not fit. -/
theorem dbound1_cons_neg {x : D} {p : Part} (hp : ¬ G.Fitp x p) (rs : List Part) :
    G.dbound1 (p :: rs) x = G.dbound1 rs x := dcount_cons_neg hp rs

omit [Finite D] in
/-- Sorting the rules against a part that `x` fits does not change how many of
them fit at `x`. -/
theorem sortDrulesRec_dbound1 {x : D} {p : Part} (hp : G.Fitp x p) :
    ∀ (ru : List Part) (n : ℕ) (rs : List Part),
      (sortDrulesRec p n rs ru).nbForced + G.dbound1 (sortDrulesRec p n rs ru).straddling x
        = n + G.dbound1 rs x + G.dbound1 ru x := by
  intro ru
  induction ru with
  | nil => intro n rs; simp [sortDrulesRec, dbound1]
  | cons p' ru ih =>
    intro n rs
    have hcmp := G.fitp_cmp hp p'
    simp only [sortDrulesRec]
    rcases hc : p.cmp p' with _ | _ | _
    · have hf : ¬ G.Fitp x p' := by
        rw [hc] at hcmp
        exact fun h => hcmp.mp h
      rw [ih, G.dbound1_cons_neg hf]
    · by_cases hf : G.Fitp x p'
      · rw [ih, G.dbound1_cons_pos hf, G.dbound1_cons_pos hf]
        omega
      · rw [ih, G.dbound1_cons_neg hf, G.dbound1_cons_neg hf]
    · have hf : G.Fitp x p' := by
        rw [hc] at hcmp
        exact hcmp.mpr trivial
      rw [ih, G.dbound1_cons_pos hf]
      omega

omit [Finite D] in
/-- The rules that fit at a hub `x` fitting `p` are the rules forced by `p`
together with the straddling rules that fit. -/
theorem sort_dbound1_eq {x : D} {p : Part} (hp : G.Fitp x p) (ru : List Part) :
    G.dbound1 ru x
      = (sortDrules p ru).nbForced + G.dbound1 (sortDrules p ru).straddling x := by
  have h := G.sortDrulesRec_dbound1 hp ru 0 []
  simpa [sortDrules, dbound1] using h.symm

/-! #### The converse of a rule

`converse_part` and `fitp_converse` are not part of the `Part` port, so the
converse operation and its correctness are parameters of the statements
below. -/

/-- The specification of the reference's `converse_part` operation: a dart
fitting `p` exactly makes the converse part fit two faces across the edge. -/
def ConverseSpec (conv : Part → PRange × Part) : Prop :=
  ∀ (p : Part) (y : D), G.ExactFitp y p →
    (conv p).1.Mem (G.arity (G.invFace2 (G.edge (G.face (G.face y))))) ∧
      G.Fitp (G.invFace2 (G.edge (G.face (G.face y)))) (conv p).2

variable {conv : Part → PRange × Part}

omit [Finite D] in
/-- The charge entering the face of `x` across the edge at `face² x` is at most
the number of target rules that fit at `x`. -/
theorem dscore1_le_dbound1_target (hplain : G.Plain) (hconv : G.ConverseSpec conv)
    {x : D} {n : ℕ} (hx : G.arity x = n) :
    G.dscore1 (G.edge (G.face (G.face x)))
      ≤ G.dbound1 (pickTargetDrules conv n theDrules) x := by
  set y := G.invFace2 (G.edge (G.face (G.face x))) with hy
  have hkey : G.invFace2 (G.edge (G.face (G.face y))) = x := by
    rw [hy, G.face_face_invFace2, hplain.edge_edge, G.invFace2_face_face]
  have key : ∀ rs : List Part,
      dcount (G.ExactFitp y) rs ≤ G.dbound1 (pickTargetDrules conv n rs) x := by
    intro rs
    induction rs with
    | nil => simp [pickTargetDrules, dbound1]
    | cons r rs ih =>
      by_cases hr : G.ExactFitp y r
      · obtain ⟨hu, hfit⟩ := hconv r y hr
        rw [hkey, hx] at hu
        rw [hkey] at hfit
        rw [dcount_cons_pos hr, pickTargetDrules_cons_pos hu, dbound1,
          dcount_cons_pos hfit, ← dbound1]
        omega
      · rw [dcount_cons_neg hr]
        refine ih.trans ?_
        by_cases hu : (conv r).1.Mem n
        · rw [pickTargetDrules_cons_pos hu, dbound1, dbound1]
          exact dcount_le_cons _ _ _
        · rw [pickTargetDrules_cons_neg hu]
  exact key theDrules

omit [Finite D] in
/-- The net charge crossing the edge at `face² x` is bounded by the difference
of the target and source rules fitting at `x`. -/
theorem dbound2_le (hplain : G.Plain) (hconv : G.ConverseSpec conv) {x : D} {n : ℕ}
    (hx : G.arity x = n) :
    G.dscore2 (G.face (G.face x))
      ≤ G.dbound2 (pickTargetDrules conv n theDrules) (pickSourceDrules n theDrules) x := by
  rw [dscore2, dbound2, ← G.dbound1_eq hx]
  have h := G.dscore1_le_dbound1_target hplain hconv hx
  omega

omit [Finite D] in
/-- The initial charge of a face of arity `n` is `60 - 10 * n`. -/
theorem dboundK_eq {x : D} {n : ℕ} (hx : G.arity x = n) :
    dboundK n = 60 - 10 * (G.arity x : ℤ) := by
  rw [hx, dboundK]

/-! #### The two consequences of a positive charge -/

omit [Finite D] in
/-- A uniform bound on the charge leaving a dart bounds the arity of a
positively charged face. -/
theorem dscore_cap1 {m : ℕ} (hm : ∀ y : D, G.dscore1 y ≤ m) {x : D} (hx : 0 < G.dscore x)
    {d : ℕ} (hd : 59 < (10 - (m : ℤ)) * d) : G.arity x < d := by
  rcases Nat.lt_or_ge (G.arity x) d with h | h
  · exact h
  exfalso
  have h10 : (0 : ℤ) < 10 - m := by
    rcases lt_or_ge (0 : ℤ) (10 - m) with h10 | h10
    · exact h10
    · exact absurd hd (not_lt.mpr (le_trans
        (mul_nonpos_of_nonpos_of_nonneg h10 (Int.natCast_nonneg d)) (by norm_num)))
  have hsum : ((orbitList G.face x).map G.dscore2).sum ≤ (G.arity x : ℤ) * m := by
    have hb : ∀ a ∈ orbitList G.face x, G.dscore2 a ≤ (m : ℤ) := by
      intro a _
      have h1 : (G.dscore1 (G.edge a) : ℤ) ≤ m := Int.ofNat_le.mpr (hm _)
      have h2 : (0 : ℤ) ≤ (G.dscore1 a : ℤ) := Int.natCast_nonneg _
      rw [dscore2]
      omega
    have hlen := sum_map_le_const hb
    rwa [G.length_orbitList_face] at hlen
  have hmul : (10 - (m : ℤ)) * d ≤ (10 - (m : ℤ)) * (G.arity x : ℤ) :=
    mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr h) h10.le
  have hexp : (10 - (m : ℤ)) * (G.arity x : ℤ)
      = 10 * (G.arity x : ℤ) - (G.arity x : ℤ) * m := by ring
  rw [dscore] at hx
  linarith

/-- A positive charge stays positive when the transfers are replaced by their
bounds. -/
theorem dscore_cap2 (hplain : G.Plain) (hconv : G.ConverseSpec conv) {x : D} {n : ℕ}
    (hx : G.arity x = n) (hpos : 0 < G.dscore x) :
    0 < dboundK n + ((orbitList G.face x).map
      (G.dbound2 (pickTargetDrules conv n theDrules) (pickSourceDrules n theDrules))).sum := by
  have hstep : ((orbitList G.face x).map G.dscore2).sum
      ≤ ((orbitList G.face x).map
        (G.dbound2 (pickTargetDrules conv n theDrules)
          (pickSourceDrules n theDrules))).sum := by
    rw [← G.sum_map_face_face x G.dscore2]
    refine sum_map_le fun z hz => ?_
    exact G.dbound2_le hplain hconv (by rw [← G.arity_cface (mem_orbitList.mp hz)]; exact hx)
  rw [dscore] at hpos
  rw [G.dboundK_eq hx]
  linarith

/-! ### Mirroring

Reflecting the map exchanges each discharge rule with its reflection across the
third spoke, and `symmetrizeDrules` has put that reflection in the list; so a
dart carries the same charge in the mirror map.  This is the reference's
`dscore_mirror`, and it is what lets a presentation script reuse a case already
settled for the reflected part.
-/

/-- Turning a part back by all but one subpart moves the dart one face on. -/
theorem exactFitp_rot_pred {q : Part} (hq : 0 < q.size) (x : D) :
    G.ExactFitp x (q.rot (q.size - 1)) ↔ G.ExactFitp (G.face x) q := by
  by_cases harity : G.arity x = q.size
  · have hx : G.face^[q.size - 1] (G.face x) = x := by
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hq, ← harity,
        G.iterate_face_arity]
    have h5 := G.exact_fitp_rot (n := q.size - 1) (p := q) (by omega) (G.face x)
    rw [hx] at h5
    exact h5.symm
  · constructor
    · intro h
      exact absurd (by simpa using h.1) harity
    · intro h
      exact absurd (by rw [← G.arity_face x]; exact h.1) harity

/-- The reflection of a rule has its size. -/
private theorem size_rot_iterate (p : Part) : ∀ i : ℕ,
    ((fun q => q.rot (p.size - 1))^[i] p.mirror).size = p.size := by
  intro i
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply']; simpa using ih

private theorem exactFitp_rot_iterate {p : Part} (hp : 0 < p.size) :
    ∀ (i : ℕ) (x : D), G.ExactFitp x ((fun q => q.rot (p.size - 1))^[i] p.mirror)
      ↔ G.ExactFitp (G.face^[i] x) p.mirror := by
  intro i
  induction i with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    have hsz := size_rot_iterate p i
    have hstep := G.exactFitp_rot_pred (q := (fun q => q.rot (p.size - 1))^[i] p.mirror)
      (by rw [hsz]; exact hp) x
    rw [hsz] at hstep
    rw [Function.iterate_succ_apply', hstep, ih, ← Function.iterate_succ_apply]

/-- A rule fits at a dart exactly when its mirror image fits five faces on. -/
theorem exactFitp_reflectDrule {p : Part} (hp : 0 < p.size) (x : D) :
    G.ExactFitp x (reflectDrule p) ↔ G.ExactFitp (G.face^[5] x) p.mirror :=
  G.exactFitp_rot_iterate hp 5 x

omit [Finite D] in
/-- Two faces back in the mirror map is two faces on in the map. -/
theorem mirror_invFace2 (x : D) : G.mirror.invFace2 x = G.face (G.face x) := by
  simp [invFace2]

omit [Finite D] in
/-- Five faces on from two faces back is three faces on. -/
theorem iterate_five_invFace2 (x : D) : G.face^[5] (G.invFace2 x) = G.face^[3] x := by
  change G.face^[3] (G.face (G.face (G.invFace2 x))) = G.face^[3] x
  rw [G.face_face_invFace2]

omit [Finite D] in
/-- Counting through a cons with matching predicates. -/
private theorem dcount_cons_congr {P Q : Part → Prop} {p q : Part} {rs rs' : List Part}
    (h : P p ↔ Q q) (hrest : dcount P rs = dcount Q rs') :
    dcount P (p :: rs) = dcount Q (q :: rs') := by
  by_cases hp : P p
  · rw [dcount_cons_pos hp, dcount_cons_pos (h.mp hp), hrest]
  · rw [dcount_cons_neg hp, dcount_cons_neg (fun hq => hp (h.mpr hq)), hrest]

omit [Finite D] in
/-- A count does not depend on the order of the list. -/
private theorem dcount_perm {P : Part → Prop} {rs rs' : List Part} (h : rs.Perm rs') :
    dcount P rs = dcount P rs' := h.countP_eq _

variable {G}

/-- The mirror image of a rule fits the mirror map where the rule fits. -/
theorem exactFitp_mirror_reflectDrule (hp : G.Plain) (hc : G.Cubic) {p : Part}
    (hsz : 0 < p.size) (y : D) :
    G.ExactFitp y (reflectDrule p) ↔ G.mirror.ExactFitp (G.face^[5] y) p := by
  rw [G.exactFitp_reflectDrule hsz y, fitp_mirror G hp hc]

/-- The rule itself fits the mirror map where its reflection does. -/
theorem exactFitp_mirror_of_reflectDrule (hp : G.Plain) (hc : G.Cubic) {p : Part}
    (hsz : 0 < p.size) (y : D) :
    G.ExactFitp y p ↔ G.mirror.ExactFitp (G.face^[5] y) (reflectDrule p) := by
  have hpm : G.mirror.Plain := (plain_mirror G).mpr hp
  have hcm : G.mirror.Cubic := (cubic_mirror G).mpr hc
  have h := G.mirror.exactFitp_mirror_reflectDrule hpm hcm hsz (G.face^[5] y)
  rw [mirror_mirror] at h
  have hback : G.mirror.face^[5] (G.face^[5] y) = y := by simp
  rw [hback] at h
  exact h.symm

/-- The mirror map counts the same rules as the map, because the rule list is
closed under reflection. -/
theorem dcount_symmetrizeDrules_mirror (hp : G.Plain) (hc : G.Cubic) (y : D) :
    ∀ rs : List Part, (∀ p ∈ rs, 0 < p.size) →
      dcount (G.mirror.ExactFitp (G.face^[5] y)) (symmetrizeDrules rs)
        = dcount (G.ExactFitp y) (symmetrizeDrules rs) := by
  intro rs
  induction rs with
  | nil => intro _; rfl
  | cons p rs ih =>
    intro hsz
    have hp0 : 0 < p.size := hsz p List.mem_cons_self
    have hrest := ih fun q hq => hsz q (List.mem_cons_of_mem p hq)
    have hA : G.mirror.ExactFitp (G.face^[5] y) p ↔ G.ExactFitp y (reflectDrule p) :=
      (exactFitp_mirror_reflectDrule hp hc hp0 y).symm
    have hB : G.mirror.ExactFitp (G.face^[5] y) (reflectDrule p) ↔ G.ExactFitp y p :=
      (exactFitp_mirror_of_reflectDrule hp hc hp0 y).symm
    rw [symmetrizeDrules]
    split
    · rename_i hsub
      -- a symmetric rule: the two fits agree
      have hcmp : G.ExactFitp y (reflectDrule p) ↔ G.ExactFitp y p := by
        constructor
        · intro h
          have hm : G.mirror.ExactFitp (G.face^[5] y) p := hA.mpr h
          have hm' : G.mirror.ExactFitp (G.face^[5] y) (reflectDrule p) :=
            ⟨by rw [hm.1, size_reflectDrule], G.mirror.fitp_cmp_subset p _ _ hsub hm.2⟩
          exact hB.mp hm'
        · intro h
          exact ⟨by rw [h.1, size_reflectDrule], G.fitp_cmp_subset p _ _ hsub h.2⟩
      exact dcount_cons_congr (hA.trans hcmp) hrest
    · -- an asymmetric rule: the two fits are exchanged
      refine (dcount_cons_congr hB (dcount_cons_congr hA hrest)).trans ?_
      exact dcount_perm (List.Perm.swap _ _ _)

/-- The charge leaving a dart is the same in the mirror map, read one face on. -/
theorem dscore1_mirror (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.mirror.dscore1 (G.face x) = G.dscore1 x := by
  rw [dscore1, dscore1, mirror_invFace2, theDrules]
  have h := dcount_symmetrizeDrules_mirror hp hc (G.invFace2 x) baseDrules
    fun q hq => lt_of_lt_of_le (by norm_num) (size_mem_baseDrules hq).1
  rw [iterate_five_invFace2] at h
  have h3 : G.face (G.face (G.face x)) = G.face^[3] x := rfl
  rw [h3]
  exact h

/-- The net transfer across an edge is the same in the mirror map. -/
theorem dscore2_mirror_face (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.mirror.dscore2 (G.face y) = G.dscore2 y := by
  rw [dscore2, dscore2, dscore1_mirror hp hc]
  congr 2
  change G.mirror.dscore1 (G.face (G.node (G.face y))) = G.dscore1 (G.edge y)
  rw [hp.node_face, dscore1_mirror hp hc]

/-- A sum over a face is unchanged by shifting the darts one face on. -/
theorem sum_map_face (x : D) (f : D → ℤ) :
    ((orbitList G.face x).map fun y => f (G.face y)).sum = ((orbitList G.face x).map f).sum :=
  calc ((orbitList G.face x).map fun y => f (G.face y)).sum
      = (((orbitList G.face x).map G.face).map f).sum := by rw [List.map_map]; rfl
    _ = ((orbitList G.face x).map f).sum := ((G.perm_map_face x).map f).sum_eq

/-- The mirror map has the same face orbits. -/
theorem perm_orbitList_mirror (x : D) :
    (orbitList G.mirror.face x).Perm (orbitList G.face x) :=
  (List.perm_ext_iff_of_nodup (nodup_orbitList _ _) (nodup_orbitList _ _)).mpr fun a => by
    simp [mem_orbitList, mirror_face, Equiv.Perm.sameCycle_inv]

/-- The charge of a face is the same in the mirror map. -/
theorem dscore_mirror (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.mirror.dscore x = G.dscore x := by
  rw [dscore, dscore, arity_mirror]
  congr 1
  rw [((perm_orbitList_mirror x).map G.mirror.dscore2).sum_eq, ← sum_map_face x G.mirror.dscore2]
  exact congrArg List.sum (List.map_congr_left fun y _ => dscore2_mirror_face hp hc y)

end Hypermap

end FourColor

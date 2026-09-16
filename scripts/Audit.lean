import FourColor.TheQuizTree
import FourColor.Configurations
import FourColor.Present
import FourColor.RedpartSound
import FourColor.Bulk.Cfg.Hyb033
import FourColor.RealPlaneMathlib

/-! # Anti-vacuity audit

`check.sh` shows the development has no `sorry`, no compiled-evaluation escape
hatch and no non-standard assumptions.  That is necessary and not sufficient: a proof can be
perfectly sound and still worthless if the *checkers* it relies on accept
everything, or if the statement is weaker than it looks.

So this file is a set of **negative controls**, kernel-verified.  Each says that
some decision procedure the proof depends on says `false` somewhere.  If any
becomes unprovable, a checker has degenerated into a tautology and the
corresponding part of the proof is vacuous.

Not part of the proof; nothing imports it.
-/

namespace FourColor

/-! ## The reducibility oracle is not constantly `true`

`succeed_by_reducibility` closes a case whenever `theRedpart p = true`.  If
`theRedpart` were constantly `true`, every presentation would succeed for free.
A free part carries no information, so it must not be accepted. -/

example : theRedpart (Part.free 5) = false := by decide +kernel
example : theRedpart (Part.free 6) = false := by decide +kernel
example : theRedpart (Part.free 11) = false := by decide +kernel

/-! ## The quiz tree is the real one

`theQuizTree` is a literal proved equal to the computed tree.  Its size matching
the reference's is an independent check that the data is the configurations'
and not, say, an empty tree that trivially answers every query. -/

example : QuizTree.size theQuizTree = 3361 := by decide +kernel

/-! ## `ExactFitp` is not vacuous

If no dart ever fitted any part, `RedpartSound` would hold trivially and the
presentations would prove nothing.  The free part of arity `n` fits every dart
of arity `n` in a pentagonal map — `exact_fitp_free` — so fitting is inhabited
as a matter of proof, not of computation. -/

#check @Hypermap.exact_fitp_free

/-! ## Configuration data is present and of the expected size -/

example : theConfigs.length = 633 := by decide +kernel

/-! ## The discharging check discriminates

`succeed_by_hubcap` closes a case whenever `hubcapFit` accepts the hubcap.  If
`hubcapFit` accepted everything, every `Hubcap` step of every presentation would
succeed for free, and the presentations would prove nothing about discharging.

The two controls below are a pair: the same checker, on the same unconstrained
part, says `false` for a bound it cannot justify and `true` for one it can.  So
it is neither constantly `true` (which would make the steps vacuous) nor
constantly `false` (which would make these controls vacuous instead).

A bound of `-1` on the net charge transferred to a dart of a free part asserts
that charge always flows *away* from it, which nothing in the rules gives; a
bound of `9` is the trivially true one, since the scores are bounded. -/

example :
    hubcapFit theRedpart (druleFork Part.conversePart 5) (Part.free 5)
      (Hubcap.one 0 (-1) <| Hubcap.nil) = false := by decide +kernel

example :
    hubcapFit theRedpart (druleFork Part.conversePart 5) (Part.free 5)
      (Hubcap.one 0 9 <| Hubcap.nil) = true := by decide +kernel

/-- The dual bounds discriminate too, at the arity the presentations work
hardest at. -/
example :
    hubcapFit theRedpart (druleFork Part.conversePart 10) (Part.free 10)
      (Hubcap.two 2 6 6 <| Hubcap.nil) = false := by decide +kernel

/-! ## The reducibility checkers discriminate

Every reducibility theorem is `cfReducible_of_bulkChecks` or
`cfReducible_of_hybridT` applied to generated data.  The checks those theorems
take are the only thing standing between a file of numbers and a theorem, so
each is exercised here on configuration 34 (`Hyb033`, a small hybrid
configuration whose every check is fast): the real data is accepted — that is
what its module proves — and a corruption of each kind of data is refused.

* The bulk rank planes: with no planes at all every trace has the top rank, so
  nothing is certified and the colourings are not at rank zero.
* The pair check: asked to justify every trace at once (a full choice mask), it
  refuses, since a colouring has no flip below rank zero.
* The residual walk: with no rank levels the leaf test cannot name a witness,
  and the walk over the certified traces fails.
* The settling lists: a chord's list must reproduce the chord's mask; an empty
  list for a chord that settles something is refused.
* The free witnesses: the entries are not known to the bulk certificate, so
  declaring them free is refused.
* The contract: without the residual entries the contract colourings are not
  all known, which is why the residual walk exists at all.
* The masks: a universe with no colours at all is not consistent. -/

open Bulk Masks in
example : goodCheck Hyb033.dm [] Hyb033.cf.prog = false := by decide +kernel

open Bulk in
example : contractCheck Hyb033.cf Hyb033.dm [] = false := by decide +kernel

open Bulk in
example :
    pairOk Hyb033.dm 0 1 Hyb033.R Hyb033.H (2 ^ 3 ^ Hyb033.dm - 1) = false := by decide +kernel

open Bulk in
example :
    pairOk Hyb033.dm 0 1 Hyb033.R Hyb033.H (pairChoice Hyb033.dm Hyb033.R Hyb033.C 0 1) = true := by
  decide +kernel

open Bulk Masks in
example :
    Hyb033.ms.walkC Cfg033.okf [] (List.range Hyb033.ms.len) [] Hyb033.ms.full Cfg033.certMask
      = false := by decide +kernel

open Bulk in
example :
    okCheckT Hyb033.ms Hyb033.dm Hyb033.P Cfg033.certMask (Cfg033.okf 0 1)
      (okBig Hyb033.dm 0 1 Hyb033.R' Hyb033.H') [] = false := by decide +kernel

open Bulk in
example :
    freeCheckT Hyb033.ms Hyb033.dm Hyb033.P (knownMask Hyb033.dm Hyb033.R) Cfg033.certMask 0 17
      = false := by decide +kernel

open Bulk in
example : contractCheckH Hyb033.cf Hyb033.dm Hyb033.R 0 = false := by decide +kernel

open Masks in
example : (⟨Cfg033.n, Cfg033.width, fun _ _ => 0⟩ : Masks).consistentCheck = false := by
  decide +kernel

/-! ## The statement is not trivially satisfiable

A colouring must be a map at least as coarse as the one coloured and must
separate adjacent regions, and `ColorableWith n` asks for at most `n` of its
regions.  The control here is about the counting, which is where a vacuous
reading would hide: `AtMostRegions` really bounds the number of regions.  The
map with two one-point regions has at most two regions and not at most one. -/

/-- Two one-point regions, at the origin and at `(1, 0)`. -/
def twoPoints : PlaneMap := fun z => if z = (0, 0) ∨ z = (1, 0) then {z} else ∅

theorem twoPoints_atMost2 : AtMostRegions 2 twoPoints := by
  refine ⟨fun i => if i = 0 then (0, 0) else (1, 0), ?_⟩
  intro z hz
  simp only [cover, twoPoints, Set.mem_setOf_eq] at hz
  split at hz
  · next h =>
    rcases h with rfl | rfl
    · exact ⟨0, by norm_num, by simp [twoPoints]⟩
    · exact ⟨1, by norm_num, by simp [twoPoints]⟩
  · simp at hz

theorem twoPoints_not_atMost1 : ¬ AtMostRegions 1 twoPoints := by
  rintro ⟨f, hf⟩
  have h0 := hf (0, 0) (by simp [cover, twoPoints])
  have h1 := hf (1, 0) (by simp [cover, twoPoints])
  obtain ⟨i, hi, hi0⟩ := h0
  obtain ⟨j, hj, hj1⟩ := h1
  have hi' : i = 0 := by omega
  have hj' : j = 0 := by omega
  subst hi' hj'
  -- both points lie in the one-point region of `f 0`
  simp only [twoPoints] at hi0 hj1
  by_cases hc : f 0 = (0, 0) ∨ f 0 = (1, 0)
  · rw [if_pos hc, Set.mem_singleton_iff] at hi0 hj1
    rw [← hi0] at hj1
    have := congrArg Prod.fst hj1
    norm_num at this
  · rw [if_neg hc] at hi0
    simp at hi0

end FourColor

import FourColor.HubCap
import FourColor.Coloring

/-!
Translated from `FourColor/Present.lean` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.

# Presentations: the scripting vocabulary for unavoidability

The unavoidability half of the proof is a large case analysis, one script per
hub arity, which whittles a part down until every case is closed either by
reducibility or by a hubcap.  This file provides the four steps such a script
takes, as lemmas about the predicate `SucceedsIn p₀ p`: "if every hub fitting
`p₀` also fits `p`, then no hub fits `p`".

* a **split** replaces a goal by the two halves of an arity range;
* a **similarity** closes a goal by a case already settled, up to rotation and
  reflection;
* a **hubcap** closes a goal by the discharging bounds of `FourColor.HubCap`;
* a **reducibility** check closes a goal by finding a reducible configuration —
  that step needs `redpart` and the embedding theorem, so it is stated here
  with the reducibility test as a parameter.

## Main definitions

* `ValidHub` — a dart of a minimal counter-example whose face has positive
  charge.
* `Successful`, `ForcedPart`, `SucceedsIn`, `ExcludedArity` — the shape of a
  presentation subgoal.

## Main results

* `exclude_arity` — a successful presentation for the free part of arity `n`
  excludes that arity.
* `succeed_by_split`, `succeed_by_similarity`, `succeed_by_hubcap`.
-/

namespace FourColor

open Hypermap

/-- A hub of a counter-example: a dart of a minimal counter-example whose face
carries a positive charge.

The reference's `valid_hub` has only the first and third fields; pentagonality
is a theorem about minimal counter-examples (`min_arity` of `birkhoff.v`).
Until that file is ported it travels with the hub. -/
structure ValidHub {D : Type} [Finite D] (G : Hypermap D) (x : D) : Prop where
  /-- The map is a minimal counter-example. -/
  mce : G.MinimalCounterExample
  /-- Every face has at least five sides. -/
  pentagonal : G.Pentagonal
  /-- The face of the dart carries a positive charge. -/
  pos : 0 < G.dscore x

/-- No hub of a counter-example fits the part exactly. -/
def Successful (p : Part) : Prop :=
  ∀ {D : Type} [Finite D] (G : Hypermap D) (x : D), ValidHub G x → ¬ G.ExactFitp x p

/-- Every hub fitting `p₀` also fits `p`. -/
def ForcedPart (p₀ p : Part) : Prop :=
  ∀ {D : Type} [Finite D] (G : Hypermap D) (x : D), ValidHub G x →
    G.ExactFitp x p₀ → G.ExactFitp x p

/-- The shape of a presentation subgoal: `p` is successful as soon as it is
forced by the more general part `p₀`. -/
def SucceedsIn (p₀ p : Part) : Prop := ForcedPart p₀ p → Successful p

/-- Assuming `Red`, no hub of a counter-example has arity `n`. -/
def ExcludedArity (Red : Prop) (n : ℕ) : Prop :=
  Red → ∀ {D : Type} [Finite D] (G : Hypermap D) (x : D), ValidHub G x → G.arity x ≠ n

/-- Starting a presentation: a successful presentation for the free part of
arity `n` excludes that arity. -/
theorem exclude_arity {Red : Prop} (n : ℕ)
    (h : Red → SucceedsIn (Part.free n) (Part.free n)) : ExcludedArity Red n := by
  intro hred D _ G x hx harity
  refine h hred (fun _ _ _ hfit => hfit) G x hx ?_
  rw [← harity]
  exact G.exact_fitp_free hx.pentagonal x

/-! ### Splitting an arity range -/

instance (i : SubpartLoc) (j k : ℕ) (p : Part) : Decidable (Part.GoodSplit i j k p) := by
  unfold Part.GoodSplit
  split
  all_goals infer_instance

/-- The two halves of a split are complementary. -/
theorem splitCond_not (lo : Bool) (k n : ℕ) :
    PRange.SplitCond (!lo) k n ↔ ¬ PRange.SplitCond lo k n := by
  cases lo
  · simp only [PRange.SplitCond, Bool.not_false, Bool.cond_true, Bool.cond_false]
    omega
  · simp only [PRange.SplitCond, Bool.not_true, Bool.cond_true, Bool.cond_false]
    omega


/-- A `Pcase` step: splitting the arity range at one location of the part
replaces the goal by the two halves, the second of which may use the first as
an extra hypothesis. -/
theorem succeed_by_split (i : SubpartLoc) (j k : ℕ) (lo : Bool) {p₀ p : Part}
    (hgs : Part.GoodSplit i j k p)
    (hl : SucceedsIn
      (if Part.GoodSplit i j k p₀ then Part.splitPart i j k lo p₀
        else Part.splitPart i j k lo p) (Part.splitPart i j k lo p))
    (hr : Successful
      (if Part.GoodSplit i j k p₀ then Part.splitPart i j k lo p₀
        else Part.splitPart i j k lo p) →
      SucceedsIn p₀ (Part.splitPart i j k (!lo) p)) :
    SucceedsIn p₀ p := by
  intro hforced
  have hp0lpl : ForcedPart
      (if Part.GoodSplit i j k p₀ then Part.splitPart i j k lo p₀
        else Part.splitPart i j k lo p) (Part.splitPart i j k lo p) := by
    intro D _ G x hx hfit
    by_cases hgs0 : Part.GoodSplit i j k p₀
    · simp only [hgs0, ite_true] at hfit
      rw [G.exact_fitp_split hx.pentagonal i j k p₀ hgs0 lo x] at hfit
      rw [G.exact_fitp_split hx.pentagonal i j k p hgs lo x]
      exact ⟨hfit.1, hforced G x hx hfit.2⟩
    · simp only [hgs0, ite_false] at hfit
      exact hfit
  have hplok : Successful (Part.splitPart i j k lo p) := hl hp0lpl
  have hprok : Successful (Part.splitPart i j k (!lo) p) := by
    refine hr (fun G x hx hfit => hplok G x hx (hp0lpl G x hx hfit)) ?_
    intro D _ G x hx hfit
    have h1 := hplok G x hx
    rw [G.exact_fitp_split hx.pentagonal i j k p hgs lo x] at h1
    rw [G.exact_fitp_split hx.pentagonal i j k p hgs (!lo) x]
    have h2 : G.ExactFitp x p := hforced G x hx hfit
    exact ⟨(splitCond_not lo k _).mpr fun hc => h1 ⟨hc, h2⟩, h2⟩
  intro D _ G x hx hfit
  have h1 := hplok G x hx
  have h2 := hprok G x hx
  rw [G.exact_fitp_split hx.pentagonal i j k p hgs lo x] at h1
  rw [G.exact_fitp_split hx.pentagonal i j k p hgs (!lo) x] at h2
  by_cases hc : PRange.SplitCond lo k (G.arity (i.dart G (G.face^[j] x)))
  · exact h1 ⟨hc, hfit⟩
  · exact h2 ⟨(splitCond_not lo k _).mpr hc, hfit⟩

/-! ### Reusing a case already settled -/

/-- Mirroring a hub gives a hub of the mirror map. -/
theorem ValidHub.mirror {D : Type} [Finite D] {G : Hypermap D} {x : D} (h : ValidHub G x) :
    ValidHub G.mirror x where
  mce := h.mce.mirror
  pentagonal := fun y => by rw [arity_mirror]; exact h.pentagonal y
  pos := by rw [dscore_mirror h.mce.plain h.mce.cubic]; exact h.pos

/-- Turning a hub around its face gives a hub. -/
theorem ValidHub.iterate_face {D : Type} [Finite D] {G : Hypermap D} {x : D}
    (h : ValidHub G x) (n : ℕ) : ValidHub G (G.face^[n] x) where
  mce := h.mce
  pentagonal := h.pentagonal
  pos := by
    rw [← G.dscore_cface (show G.CFace x (G.face^[n] x) from ⟨n, by simp [Equiv.Perm.coe_pow]⟩)]
    exact h.pos

/-- A `Similar to` step: a goal is closed by a case already settled, up to a
rotation and possibly a reflection of the part. -/
theorem succeed_by_similarity (j : ℕ) (mir : Bool) {ps : Part} (hps : Successful ps)
    {p₀ p : Part} (hj : j ≤ p.size)
    (hsz : ps.size = (Part.rot j (if mir then p.mirror else p)).size)
    (hcmp : (Part.rot j (if mir then p.mirror else p)).cmp ps = .subset) :
    SucceedsIn p₀ p := by
  intro _ D _ G x hx hfit
  -- pass to the mirror map if the similarity is a reflection
  cases mir with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hsz hcmp
    have hfit2 : G.ExactFitp (G.face^[j] x) (Part.rot j p) :=
      (G.exact_fitp_rot (by rw [← hfit.1] at hj ⊢; exact hj) x).mp hfit
    exact hps G _ (hx.iterate_face j) ⟨by rw [hfit2.1, hsz],
      G.fitp_cmp_subset _ _ _ hcmp hfit2.2⟩
  | true =>
    simp only [ite_true] at hsz hcmp
    have hmfit : G.mirror.ExactFitp x p.mirror := by
      have h := fitp_mirror G hx.mce.plain hx.mce.cubic x p.mirror
      rw [Part.mirror_mirror] at h
      exact h.mp hfit
    have hj' : j ≤ p.mirror.size := by rwa [Part.size_mirror]
    have hfit2 : G.mirror.ExactFitp (G.mirror.face^[j] x) (Part.rot j p.mirror) :=
      (G.mirror.exact_fitp_rot (by rw [← hmfit.1] at hj' ⊢; exact hj') x).mp hmfit
    exact hps G.mirror _ ((hx.mirror).iterate_face j) ⟨by rw [hfit2.1, hsz],
      G.mirror.fitp_cmp_subset _ _ _ hcmp hfit2.2⟩

/-! ### Closing a case by reducibility

The reducibility test itself is `redpart` of `FourColor.RedPart`, and its
soundness is the embedding theorem of `embed.v`; both are stated elsewhere, so
the test and its soundness are parameters here.
-/

/-- Soundness of a reducibility test: a part the test accepts fits no dart of a
minimal counter-example. -/
def RedpartSound (redp : Part → Bool) : Prop :=
  ∀ {D : Type} [Finite D] (G : Hypermap D), G.MinimalCounterExample →
    ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q

/-- A `Reducible` step: a part the reducibility test accepts is successful. -/
theorem succeed_by_reducibility {redp : Part → Bool} (hred : RedpartSound redp)
    {p₀ p : Part} (h : redp p = true) : SucceedsIn p₀ p := by
  intro _ D _ G x hx
  exact hred G hx.mce x p h

/-! ### Closing a case by discharging -/

/-- The converse-part operation of `FourColor.Part` meets the specification the
discharging bounds need. -/
theorem converseSpec_conversePart {D : Type} [Finite D] {G : Hypermap D} (hp : G.Plain)
    (hc : G.Cubic) (hG : G.Pentagonal) : G.ConverseSpec Part.conversePart :=
  fun p y hfit => fitp_converse G hp hc hG p y hfit

/-- A `Hubcap` step: a covering hubcap whose bounds all check closes the goal.

The reducibility test is a parameter, as in the reference: the test itself is
`redpart`, and its soundness is the embedding theorem, which is proved
elsewhere. -/
theorem succeed_by_hubcap {redp : Part → Bool} (hredp : RedpartSound redp)
    (hc : Hubcap) {p₀ p : Part} (h2 : 2 ≤ p.size)
    (hcover : hubcapCover p.size hc = true)
    (hfitc : hubcapFit redp (druleFork Part.conversePart p.size) p hc = true) :
    SucceedsIn p₀ p := by
  intro _ D _ G x hx
  exact not_exactFitp_of_hubcap hx.mce.plain
    (converseSpec_conversePart hx.mce.plain hx.mce.cubic hx.pentagonal)
    (fun y q hq => hredp G hx.mce y q hq) rfl h2 hx.pos hcover hfitc

end FourColor

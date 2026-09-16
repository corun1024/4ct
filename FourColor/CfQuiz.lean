import FourColor.CfMap
import FourColor.Quiz
import FourColor.Patch

/-!
# The quiz of a configuration

This module compiles the quiz that tests for the occurrence of a configuration
in a map: the bridge between the configuration maps of `FourColor.CfMap` and
the question trees of `FourColor.Quiz`.

The algorithm walks the construction program of the configuration *forwards*
(that is, backwards along the map construction, which runs right to left),
keeping a list of `RingQuestion`s: one for each dart of the ring of the
intermediate map, recording the question that tests the kernel faces already
detached from that ring, the number of faces the dart still has to acquire, and
whether the dart ends up in the kernel.  Each `Y` step merges two of these
questions into one, each `H` step redistributes three of them; when the program
is exhausted the two remaining questions form the quiz.

Since this requires computing arities, the arities are checked along the way:
kernel faces must have between 5 and 11 sides (only the hub may have more than
8), and ring faces between 3 and 6 sides.  The procedure is valid but not
complete — for instance it assumes that skews occur only at articulations, and
it refuses to join two trees at an `H` step — so it simply returns the invalid
quiz `noquiz` when it meets a case it cannot handle.  The configuration data is
knobbed so that this never happens for the programs actually used, which is
checked by evaluating `cfquiz` on each of them.

## Main definitions

* `smallQArity`, `largeQArity`, `BadSmallArity`, `BadRingArity` — the arity
  checks, all offset by two because a face detached from the submap ring
  already has two neighbours there.
* `RingQuestion` — the question attached to one dart of the ring of an
  intermediate map, with its outer arity and its kernel flag.
* `rqsY`, `cfquizY`, `rqsH`, `cfquizH` — one step of the compilation.
* `cfquizRec`, `cfquiz` — the compiler, and the quiz of a configuration.
* `cpradius2` — the radius-2 check on the kernel of a configuration.
* `rqsFit`, `rqsWalk`, `RqsProper` — the invariant relating a list of ring
  questions to the darts of the ring it describes.

## Main results

* `badSmallArity_smallQArity`, `toNat_largeQArity_eq_iff` — the arity tables
  return the intended value exactly on the intended range.
* `goodRingArity_of_not_badRingArity` — the ring arity check implies
  `Hypermap.GoodRingArity`.
* `radius2_of_cpradius2`, `cpradius2P` — the radius-2 check is correct.
* `configProg_of_isQuizR`, `ConfigProg.of_cfquiz` — if the compiler returns a
  valid (right) quiz then its input really was a configuration program.  This is
  how the dynamic check on the 633 configuration programs is turned into a
  proof.
* `rqsFit_append`, `rqsWalk_append`, `rqsFit_rotate`, `rqsWalk_rotate` — the
  list algebra of the invariant, in particular its behaviour under the `R n`
  step of the compilation.
* `rqsProper_R`, `rqsProper_Y`, `rqsProper_H` — each step of the compilation
  preserves the invariant.
* `cfquizRec_nil_valid`, `cfquizRec_valid`, `cfquizP` — **the compiler is
  correct**: the compiled quiz is a valid quiz for the perimeter of the
  configuration map, whose faces all have a good ring arity.
* `valid_cfquiz`, `embeddable_cfquiz` — the quiz of a configuration whose
  dynamic check passes is a valid quiz for its ring, and its map is
  embeddable.

The only deviation from the reference is in the `R n` step of `cfquizRec`,
which rotates the ring questions modulo the length of the list rather than by
the reference's truncating subtraction; see `cfquizRec_R`.
-/

namespace FourColor

/-! ### Arity tables

All the arity functions below work with the arities offset by two, because each
time a face is detached from the submap ring it already had two neighbours
there. -/

/-- The `QArity` of a kernel face with `a + 2` sides, for a face that is not the
hub, so that `a + 2` should lie in the range 5–8.  Outside that range the value
returned is deliberately *different* from `a + 2`, so that the single test
`BadSmallArity` also rejects the out-of-range arities. -/
def smallQArity : ℕ → QArity
  | 3 => .qa5
  | 4 => .qa6
  | 5 => .qa7
  | 6 => .qa8
  | 7 => .qa10
  | _ => .qa9

/-- A `QArity` too large for a kernel face other than the hub. -/
def BadSmallArity (qa : QArity) : Prop := 8 < qa.toNat

instance : DecidablePred BadSmallArity :=
  fun qa => inferInstanceAs (Decidable (8 < qa.toNat))

/-- The table `smallQArity` is correct exactly where it is accepted: it returns
the arity `a + 2` precisely when `BadSmallArity` does not reject it. -/
theorem badSmallArity_smallQArity (a : ℕ) :
    BadSmallArity (smallQArity a) ↔ (smallQArity a).toNat ≠ a + 2 := by
  match a with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | (n + 8) =>
    have h : smallQArity (n + 8) = QArity.qa9 := rfl
    rw [h]
    simp only [BadSmallArity, QArity.toNat, ne_eq]
    omega

/-- The `QArity` of the hub of a configuration, a kernel face with `a + 2`
sides for `a + 2` in the range 5–11.  As for `smallQArity`, out-of-range
arities get a value that differs from `a + 2`. -/
def largeQArity : ℕ → QArity
  | 7 => .qa9
  | 8 => .qa10
  | 9 => .qa11
  | a => smallQArity a

/-- The table `largeQArity` returns the arity `a + 2` exactly on the range
where `a + 2` is between 5 and 11. -/
theorem toNat_largeQArity_eq_iff (a : ℕ) :
    (largeQArity a).toNat = a + 2 ↔ 3 ≤ a ∧ a ≤ 9 := by
  match a with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | (n + 10) =>
    have h : largeQArity (n + 10) = QArity.qa9 := rfl
    rw [h]
    simp only [QArity.toNat]
    omega

/-- A ring face arity outside the range allowed for the perimeter of a
configuration: the face has `a + 2` sides, and `a + 2` must be between 3 and
6. -/
def BadRingArity (a : ℕ) : Prop := a = 0 ∨ 5 ≤ a

instance : DecidablePred BadRingArity :=
  fun a => inferInstanceAs (Decidable (a = 0 ∨ 5 ≤ a))

/-- Passing the ring arity check means having a good ring arity. -/
theorem goodRingArity_of_not_badRingArity {D : Type*} (G : Hypermap D) (x : D)
    (h : ¬ BadRingArity (G.arity x - 2)) : G.GoodRingArity x := by
  simp only [BadRingArity, not_or, Nat.not_le] at h
  exact ⟨by omega, by omega⟩

/-! ### The compiler -/

/-- The invalid quiz, returned whenever the compilation fails.  It is not a
right quiz, so `Quiz.IsQuizR` detects the failure. -/
def noquiz : Quiz := ⟨.ask0, .ask0⟩

/-- The error value is not a right quiz. -/
theorem not_isQuizR_noquiz : ¬ noquiz.IsQuizR := fun h => h.1

/-- The question testing the kernel faces reachable from one dart of the ring
of an intermediate stage of the map construction.  The question is rooted at
the node of the image of that dart in the *full* configuration map. -/
structure RingQuestion where
  /-- Whether the dart lies in the kernel of the final map. -/
  isKernel : Bool
  /-- The outer arity of the dart: the number of adjacent faces that are not in
  the current submap. -/
  outerArity : ℕ
  /-- The question testing the kernel faces already detached from the ring. -/
  question : Question

/-- The ring question a dart starts with: no face detached yet. -/
def initRingQuestion : RingQuestion := ⟨false, 0, .ask0⟩

/-- The new list of ring questions after a `Y` step, given the first and third
old ring questions, the rest `qs` of the old list, and the new question `q₁'`
for the first ring face.  The second old ring question has been absorbed into
`q₁'`. -/
def rqsY (rq₁ rq₃ : RingQuestion) (qs : List RingQuestion) (q₁' : Question) :
    List RingQuestion :=
  ⟨rq₁.isKernel, rq₁.outerArity + 1, q₁'⟩ ::
    ⟨rq₃.isKernel, rq₃.outerArity + 1, rq₃.question⟩ :: qs

/-- The ring question for the first ring face of a `Y` step, passed on to `k`
(a partly applied `rqsY`).  The step fails, returning the empty list, when the
arity checks fail or when the two questions cannot be merged. -/
def cfquizY (rq₁ rq₂ : RingQuestion) (k : Question → List RingQuestion) :
    List RingQuestion :=
  if rq₂.isKernel then
    if BadSmallArity (smallQArity rq₂.outerArity) then []
    else
      k (match rq₁.question, rq₂.question with
         | .ask0, .ask0 => .ask1 (smallQArity rq₂.outerArity)
         | .ask0, q₂ => .askL (smallQArity rq₂.outerArity) q₂
         | q₁, .ask0 => .askR (smallQArity rq₂.outerArity) q₁
         | q₁, q₂ => .askLR (smallQArity rq₂.outerArity) q₂ q₁)
  else
    if BadRingArity rq₂.outerArity then []
    else
      match rq₁.question, rq₂.question with
      | .ask0, .ask0 => k .ask0
      | .askR qa₁ q₁r, .ask0 => k (.askRR qa₁ q₁r)
      | .ask0, .askL qa₁ q₁l => k (.askLL qa₁ q₁l)
      | _, _ => []

/-- The new list of ring questions after an `H` step: the middle ring face is
new, is in the kernel, and has one outer neighbour so far. -/
def rqsH (rq₁ rq₃ : RingQuestion) (qs : List RingQuestion) (q₁' q₂' : Question) :
    List RingQuestion :=
  ⟨rq₁.isKernel, rq₁.outerArity + 1, q₁'⟩ :: ⟨true, 1, q₂'⟩ ::
    ⟨rq₃.isKernel, rq₃.outerArity + 1, rq₃.question⟩ :: qs

/-- The two ring questions for the first two ring faces of an `H` step, passed
on to `k` (a partly applied `rqsH`).  Joining two nonempty question trees at an
`H` step is not supported, and fails with the empty list; the configuration
data is chosen so that this never happens. -/
def cfquizH (rq₁ rq₂ : RingQuestion) (k : Question → Question → List RingQuestion) :
    List RingQuestion :=
  if rq₂.isKernel then
    if BadSmallArity (smallQArity (rq₂.outerArity + 1)) then []
    else
      match rq₁.question, rq₂.question, rq₁.isKernel with
      | .ask0, .ask0, true => k (.ask1 (smallQArity (rq₂.outerArity + 1))) .ask0
      | .ask0, .ask0, false => k .ask0 (.ask1 (smallQArity (rq₂.outerArity + 1)))
      | .ask0, q₂, _ => k .ask0 (.askL (smallQArity (rq₂.outerArity + 1)) q₂)
      | q₁, .ask0, _ => k (.askR (smallQArity (rq₂.outerArity + 1)) q₁) .ask0
      | _, _, _ => []
  else
    if BadRingArity (rq₂.outerArity + 1) then []
    else
      match rq₁.question, rq₂.question with
      | .ask0, .ask0 => k .ask0 .ask0
      | _, _ => []

/-- The quiz compiler: `cfquizRec cp qs` compiles the rest `cp` of a
configuration program against the list `qs` of ring questions testing for the
faces created by the part of the program already processed.  Note that `cp` is
run *right to left* by `cpmap`, so `cfquizRec` walks the map construction
backwards. -/
def cfquizRec : CProg → List RingQuestion → Quiz
  | [], rq₁ :: rq₂ :: _ =>
      if rq₁.isKernel && rq₂.isKernel then
        if (largeQArity (rq₁.outerArity - 1)).toNat = rq₁.outerArity + 1 ∧
            ¬ BadSmallArity (smallQArity (rq₂.outerArity - 1)) then
          ⟨.askR (largeQArity (rq₁.outerArity - 1)) rq₂.question,
           .askR (smallQArity (rq₂.outerArity - 1)) rq₁.question⟩
        else noquiz
      else noquiz
  | .R n :: cp, rq₁ :: rq₂ :: rq₃ :: qs =>
      cfquizRec cp
        ((rq₁ :: rq₂ :: rq₃ :: qs).rotate (qs.length + 3 - n % (qs.length + 3)))
  | .Y :: cp, rq₁ :: rq₂ :: rq₃ :: qs =>
      cfquizRec cp (cfquizY rq₁ rq₂ (rqsY rq₁ rq₃ qs))
  | .H :: cp, rq₁ :: rq₂ :: rq₃ :: qs =>
      cfquizRec cp (cfquizH rq₁ rq₂ (rqsH rq₁ rq₃ qs))
  | _, _ => noquiz

/-! ### The radius-2 check

The quiz starts at one particular face of the kernel, which need not be its
centre, so the radius of the kernel is checked separately, by a computation on
the adjacency masks of `FourColor.CfMap`: for each candidate hub, mask the
faces adjacent to it, then the faces adjacent to *those*, and check that every
kernel face has been reached. -/

/-- `cpradius2 cp i` tests the first `i` kernel faces of `cpmap cp` as possible
hubs: for each one it takes the faces adjacent to it, keeps only the kernel
ones, and checks that every kernel face is adjacent to one of them. -/
def cpradius2 (cp : CProg) : ℕ → Bool
  | 0 => false
  | i + 1 =>
      let cm0 := cfmask1 cp i
      (cpadj ⟨cm0.ring, (cpadj cm0 cp).kernel⟩ cp).kernel.all id || cpradius2 cp i

/-- The quiz that tests for the presence of a copy of the configuration map of
`cf`, or `noquiz` if the compilation fails or the kernel of `cf` is found to
have radius more than two. -/
def cfquiz (cf : Config) : Quiz :=
  if cpradius2 cf.prog (cpksize cf.prog) then
    cfquizRec cf.prog (List.replicate (cprsize cf.prog) initRingQuestion)
  else noquiz

/-! ### The compiler only accepts configuration programs

The quiz of a configuration is checked dynamically: for each of the 633
configuration programs one evaluates `cfquiz` and checks that the result is a
right quiz.  The results below turn that check into a proof, by showing that the
compiler can only return a right quiz when it is run on a configuration program
whose ring questions have the right length. -/

@[simp] theorem cfquizRec_nil_questions (cp : CProg) : cfquizRec cp [] = noquiz := by
  match cp with
  | [] => rfl
  | s :: _ => cases s <;> rfl

/-- The compiler needs at least three ring questions to consume a step. -/
theorem cfquizRec_cons_of_length_lt {s : CpStep} {cp : CProg} {qs : List RingQuestion}
    (h : qs.length < 3) : cfquizRec (s :: cp) qs = noquiz := by
  match qs with
  | [] => cases s <;> rfl
  | [_] => cases s <;> rfl
  | [_, _] => cases s <;> rfl
  | _ :: _ :: _ :: _ => simp only [List.length_cons] at h; omega

/-- An `R n` step rotates the list of ring questions.  The rotation is taken
modulo the length of the list, unlike the truncating subtraction of the
reference: the `R` step of `FourColor.CfMap` rotates the ring modulo its
length, and the two agree whenever `n` is at most the size of the ring, which
is the case for every configuration program. -/
theorem cfquizRec_R (n : ℕ) (cp : CProg) (rq₁ rq₂ rq₃ : RingQuestion)
    (qs : List RingQuestion) :
    cfquizRec (.R n :: cp) (rq₁ :: rq₂ :: rq₃ :: qs) =
      cfquizRec cp
        ((rq₁ :: rq₂ :: rq₃ :: qs).rotate (qs.length + 3 - n % (qs.length + 3))) := rfl

/-- A `Y` step merges the first two ring questions. -/
theorem cfquizRec_Y (cp : CProg) (rq₁ rq₂ rq₃ : RingQuestion) (qs : List RingQuestion) :
    cfquizRec (.Y :: cp) (rq₁ :: rq₂ :: rq₃ :: qs) =
      cfquizRec cp (cfquizY rq₁ rq₂ (rqsY rq₁ rq₃ qs)) := rfl

/-- An `H` step redistributes the first three ring questions. -/
theorem cfquizRec_H (cp : CProg) (rq₁ rq₂ rq₃ : RingQuestion) (qs : List RingQuestion) :
    cfquizRec (.H :: cp) (rq₁ :: rq₂ :: rq₃ :: qs) =
      cfquizRec cp (cfquizH rq₁ rq₂ (rqsH rq₁ rq₃ qs)) := rfl

/-- The compiler rejects any step other than `R`, `Y` and `H`. -/
theorem cfquizRec_of_not_isConfig {s : CpStep} (hs : ¬ s.IsConfig) (cp : CProg)
    (qs : List RingQuestion) : cfquizRec (s :: cp) qs = noquiz := by
  match s with
  | .R _ | .Y | .H => exact absurd trivial hs
  | .R' | .U | .K | .A =>
    match qs with
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl

/-- A `Y` step either fails or produces the questions its continuation makes. -/
theorem cfquizY_eq_nil_or (rq₁ rq₂ : RingQuestion) (k : Question → List RingQuestion) :
    cfquizY rq₁ rq₂ k = [] ∨ ∃ q, cfquizY rq₁ rq₂ k = k q := by
  rw [cfquizY]
  split_ifs <;>
    first
      | exact .inl rfl
      | exact .inr ⟨_, rfl⟩
      | (split <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩)

/-- An `H` step either fails or produces the questions its continuation makes. -/
theorem cfquizH_eq_nil_or (rq₁ rq₂ : RingQuestion)
    (k : Question → Question → List RingQuestion) :
    cfquizH rq₁ rq₂ k = [] ∨ ∃ q q', cfquizH rq₁ rq₂ k = k q q' := by
  rw [cfquizH]
  split_ifs <;>
    first
      | exact .inl rfl
      | exact .inr ⟨_, _, rfl⟩
      | (split <;> first | exact .inl rfl | exact .inr ⟨_, _, rfl⟩)

/-- A `Y` step shortens the list of ring questions by one. -/
@[simp] theorem length_rqsY (rq₁ rq₃ : RingQuestion) (qs : List RingQuestion) (q : Question) :
    (rqsY rq₁ rq₃ qs q).length = qs.length + 2 := by
  simp [rqsY]

/-- An `H` step keeps the length of the list of ring questions. -/
@[simp] theorem length_rqsH (rq₁ rq₃ : RingQuestion) (qs : List RingQuestion)
    (q q' : Question) : (rqsH rq₁ rq₃ qs q q').length = qs.length + 3 := by
  simp [rqsH]

/-- Prefixing a configuration step to a configuration program. -/
theorem configProg_cons {s : CpStep} {cp : CProg} (hs : s.IsConfig) (h : ConfigProg cp) :
    ConfigProg (s :: cp) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hs
    · exact h.1 t ht
  · have hne : cp ≠ [] := h.ne_nil
    match cp, hne with
    | _ :: _, _ => rw [List.getLast?_cons_cons]; exact h.2

/-- The one-step configuration program. -/
theorem configProg_singleton_Y : ConfigProg [CpStep.Y] := by
  refine ⟨fun t ht => ?_, rfl⟩
  simp only [List.mem_singleton] at ht
  subst ht
  exact trivial

/-- **The dynamic check is sound**: if the compiler returns a right quiz then
its input was a configuration program.  The list of ring questions must have
the length of the ring of the map the program builds. -/
theorem configProg_of_isQuizR : ∀ (cp : CProg) (qs : List RingQuestion), cp ≠ [] →
    qs.length = cprsize cp → (cfquizRec cp qs).IsQuizR → ConfigProg cp := by
  intro cp
  induction cp with
  | nil => intro _ hne; exact absurd rfl hne
  | cons s cp ih =>
    intro qs _ hlen hR
    have h3 : 3 ≤ qs.length := by
      by_contra hlt
      rw [cfquizRec_cons_of_length_lt (by omega)] at hR
      exact not_isQuizR_noquiz hR
    obtain ⟨rq₁, rq₂, rq₃, qs', rfl⟩ : ∃ a b c t, qs = a :: b :: c :: t := by
      match qs, h3 with
      | a :: b :: c :: t, _ => exact ⟨a, b, c, t, rfl⟩
    have hlen' : qs'.length + 3 = cprsize (s :: cp) := by
      simp only [List.length_cons] at hlen; omega
    cases s with
    | R n =>
      rw [cfquizRec_R] at hR
      have hcps : cprsize (CpStep.R n :: cp) = cprsize cp := rfl
      rw [hcps] at hlen'
      cases cp with
      | nil => exact absurd hlen' (by simp [cprsize])
      | cons s' cp' =>
        refine configProg_cons trivial (ih _ (by simp) ?_ hR)
        rw [List.length_rotate]
        simp only [List.length_cons]
        omega
    | Y =>
      rw [cfquizRec_Y] at hR
      have hcps : cprsize (CpStep.Y :: cp) = cprsize cp + 1 := rfl
      rw [hcps] at hlen'
      rcases cfquizY_eq_nil_or rq₁ rq₂ (rqsY rq₁ rq₃ qs') with hY | ⟨q, hY⟩
      · rw [hY, cfquizRec_nil_questions] at hR
        exact absurd hR not_isQuizR_noquiz
      · cases cp with
        | nil => exact configProg_singleton_Y
        | cons s' cp' =>
          refine configProg_cons trivial (ih _ (by simp) ?_ hR)
          rw [hY, length_rqsY]
          omega
    | H =>
      rw [cfquizRec_H] at hR
      have hcps : cprsize (CpStep.H :: cp) = cprsize cp := rfl
      rw [hcps] at hlen'
      rcases cfquizH_eq_nil_or rq₁ rq₂ (rqsH rq₁ rq₃ qs') with hH | ⟨q, q', hH⟩
      · rw [hH, cfquizRec_nil_questions] at hR
        exact absurd hR not_isQuizR_noquiz
      · cases cp with
        | nil => exact absurd hlen' (by simp [cprsize])
        | cons s' cp' =>
          refine configProg_cons trivial (ih _ (by simp) ?_ hR)
          rw [hH, length_rqsH]
          omega
    | R' =>
      rw [cfquizRec_of_not_isConfig (by simp [CpStep.IsConfig])] at hR
      exact absurd hR not_isQuizR_noquiz
    | U =>
      rw [cfquizRec_of_not_isConfig (by simp [CpStep.IsConfig])] at hR
      exact absurd hR not_isQuizR_noquiz
    | K =>
      rw [cfquizRec_of_not_isConfig (by simp [CpStep.IsConfig])] at hR
      exact absurd hR not_isQuizR_noquiz
    | A =>
      rw [cfquizRec_of_not_isConfig (by simp [CpStep.IsConfig])] at hR
      exact absurd hR not_isQuizR_noquiz

/-- A configuration whose quiz passes the dynamic check passes the radius-2
check. -/
theorem cpradius2_of_cfquiz {cf : Config} (h : (cfquiz cf).IsQuizR) :
    cpradius2 cf.prog (cpksize cf.prog) = true := by
  by_contra hb
  rw [Bool.not_eq_true] at hb
  rw [cfquiz] at h
  simp only [hb, Bool.false_eq_true, reduceIte] at h
  exact not_isQuizR_noquiz h

/-- Once the radius-2 check has passed, the quiz is the compiled one. -/
theorem cfquiz_eq_cfquizRec {cf : Config}
    (h : cpradius2 cf.prog (cpksize cf.prog) = true) :
    cfquiz cf = cfquizRec cf.prog (List.replicate (cprsize cf.prog) initRingQuestion) := by
  rw [cfquiz]
  simp only [h, reduceIte]

/-- The program of a configuration whose quiz passes the dynamic check is a
configuration program. -/
theorem ConfigProg.of_cfquiz {cf : Config} (h : (cfquiz cf).IsQuizR) : ConfigProg cf.prog := by
  rw [cfquiz_eq_cfquizRec (cpradius2_of_cfquiz h)] at h
  refine configProg_of_isQuizR cf.prog _ ?_ (by simp) h
  rintro hnil
  rw [hnil] at h
  have h2 : cprsize ([] : CProg) = 2 := rfl
  rw [h2] at h
  exact not_isQuizR_noquiz h

/-! ### The radius-2 check is correct

The check masks, for each candidate hub, the kernel faces adjacent to it and
then the faces adjacent to *those*; if the second mask covers the whole kernel,
every kernel face is two adjacency steps from the hub. -/

/-- A mask with all entries `true` selects everything. -/
private theorem listMask_eq_self {α : Type*} : ∀ (m : List Bool) (l : List α),
    m.length = l.length → (∀ b ∈ m, b = true) → listMask m l = l := by
  intro m
  induction m with
  | nil =>
    intro l hl _
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hnil
    rfl
  | cons b m ih =>
    intro l hl hall
    cases l with
    | nil => simp at hl
    | cons x l =>
      have hb : b = true := hall b List.mem_cons_self
      subst hb
      have hcons : listMask (true :: m) (x :: l) = x :: listMask m l := rfl
      rw [hcons, ih l (by simpa using hl) fun c hc => hall c (List.mem_cons_of_mem _ hc)]

/-- The kernel of the perimeter of a configuration map is exactly the band of
its kernel transversal. -/
theorem kernel_cpring_iff {cp : CProg} (hcp : ConfigProg cp) (x : (cpmap cp).Dart) :
    (cpmap cp).map.Kernel (cpmap cp).cpring x ↔ (cpmap cp).map.Fband (cpker cp) x := by
  constructor
  · intro hk
    rcases Hypermap.fband_append.mp (cpmap_cover hcp x) with hb | hb
    · exact absurd hb hk
    · exact hb
  · rintro ⟨y, hy, hxy⟩ ⟨z, hz, hxz⟩
    obtain ⟨-, -, hdis⟩ := Hypermap.simple_append.mp (cpmap_simple hcp)
    exact hdis z hz ⟨y, hy, hxz.symm.trans hxy⟩

/-- The radius-2 check on no candidate hub fails. -/
@[simp] theorem cpradius2_zero (cp : CProg) : cpradius2 cp 0 = false := rfl

/-- Unfolding the radius-2 check at one more candidate hub. -/
theorem cpradius2_succ (cp : CProg) (i : ℕ) :
    cpradius2 cp (i + 1) =
      ((cpadj ⟨(cfmask1 cp i).ring, (cpadj (cfmask1 cp i) cp).kernel⟩ cp).kernel.all id
        || cpradius2 cp i) := rfl

/-- **The radius-2 check is correct**: when it succeeds, the kernel of the
configuration map has radius two. -/
theorem radius2_of_cpradius2 {cp : CProg} (hcp : ConfigProg cp) : ∀ i, i ≤ cpksize cp →
    cpradius2 cp i = true →
    (cpmap cp).map.Radius2 {x | (cpmap cp).map.Kernel (cpmap cp).cpring x} := by
  intro i
  induction i with
  | zero => intro _ h; exact absurd h (by simp)
  | succ i ih =>
    intro hle hrad
    rw [cpradius2_succ, Bool.or_eq_true] at hrad
    rcases hrad with hrad | hrad
    swap
    · exact ih (by omega) hrad
    have hi : i < cpksize cp := by omega
    have hkerlen : (cpker cp).length = cpksize cp := size_cpker hcp
    have hcm0 : (cfmask1 cp i).Proper cp := properCfMask1 cp i
    have hcm1 : (CfMask.mk (cfmask1 cp i).ring (cpadj (cfmask1 cp i) cp).kernel).Proper cp :=
      ⟨hcm0.1, (cpadj_proper cp _ hcm0).2⟩
    have hk2len :
        (cpadj ⟨(cfmask1 cp i).ring, (cpadj (cfmask1 cp i) cp).kernel⟩ cp).kernel.length
          = cpksize cp := (cpadj_proper cp _ hcm1).2
    have hmask2 :
        listMask (cpadj ⟨(cfmask1 cp i).ring, (cpadj (cfmask1 cp i) cp).kernel⟩ cp).kernel
          (cpker cp) = cpker cp :=
      listMask_eq_self _ _ (by rw [hk2len, hkerlen]) fun b hb => by
        simpa using List.all_eq_true.mp hrad b hb
    have hx0 : cpmask (cfmask1 cp i) cp
        = [(cpker cp)[i]'(by rw [hkerlen]; exact hi)] := cpmask1 cp i hcp hi
    set x₀ := (cpker cp)[i]'(by rw [hkerlen]; exact hi) with hx₀def
    have hx₀mem : x₀ ∈ cpker cp := List.getElem_mem _
    have hring1 : listMask (cfmask1 cp i).ring (cpmap cp).cpring = [] :=
      listMask_eq_nil _ _ fun b hb => List.eq_of_mem_replicate hb
    have hcm1mask :
        cpmask ⟨(cfmask1 cp i).ring, (cpadj (cfmask1 cp i) cp).kernel⟩ cp
          = listMask (cpadj (cfmask1 cp i) cp).kernel (cpker cp) := by
      rw [cpmask, hring1, List.nil_append]
    have hE1 := cpmask_adj hcp hcm0
    have hE2 := cpmask_adj hcp hcm1
    have hker := kernel_cpring_iff hcp
    refine ⟨x₀, (hker x₀).mpr (Hypermap.fband_of_mem hx₀mem), fun x hx => ?_⟩
    have hxf : (cpmap cp).map.Fband (cpker cp) x := (hker x).mp hx
    have hx2 : (cpmap cp).map.Fband
        (cpmask (cpadj ⟨(cfmask1 cp i).ring, (cpadj (cfmask1 cp i) cp).kernel⟩ cp) cp) x := by
      rw [cpmask]
      exact Hypermap.fband_append.mpr (Or.inr (by rw [hmask2]; exact hxf))
    obtain ⟨y, hy, hxy⟩ := (hE2 x).mp hx2
    rw [hcm1mask] at hy
    have hyk : y ∈ cpker cp := mem_of_mem_listMask _ _ hy
    obtain ⟨z, hxz, hzy⟩ := hxy
    have hez : (cpmap cp).map.Fband (cpmask (cpadj (cfmask1 cp i) cp) cp)
        ((cpmap cp).map.edge z) := by
      rw [cpmask]
      exact Hypermap.fband_append.mpr (Or.inr ⟨y, hy, hzy⟩)
    have hadj0 : (cpmap cp).map.Adj ((cpmap cp).map.edge z) x₀ := by
      obtain ⟨w, hw, hadj⟩ := (hE1 _).mp hez
      rw [hx0, List.mem_singleton] at hw
      rw [← hw]
      exact hadj
    exact ⟨(cpmap cp).map.edge z, (hker _).mpr ⟨y, hyk, hzy⟩,
      (cpmap_plain hcp.cubicProg).adj_symm hadj0, ⟨z, hxz, Hypermap.rlink_edge z⟩⟩

/-- **The kernel of a configuration has radius two** as soon as its quiz passes
the dynamic check. -/
theorem cpradius2P {cf : Config} (h : (cfquiz cf).IsQuizR) :
    (cfmap cf).map.Radius2 {x | (cfmap cf).map.Kernel (cfring cf) x} := by
  have hset : {x : (cfmap cf).Dart | (cfmap cf).map.Kernel (cfring cf) x}
      = {x | (cfmap cf).map.Kernel (cfmap cf).cpring x} := by
    ext x
    exact not_congr Hypermap.fband_reverse
  rw [hset]
  exact radius2_of_cpradius2 (ConfigProg.of_cfquiz h) _ le_rfl (cpradius2_of_cfquiz h)

/-! ### Fitting a list of ring questions

The compiler maintains an invariant relating the list of ring questions to the
ring of the intermediate map.  Here `M` is that intermediate map, `M₀` the full
configuration map, and `h` the injection of the darts of `M` into those of `M₀`
(the reference's `injcp`): each question is rooted at `node (h x)` for a dart
`x` of the ring of `M`, so that `node` is computed in the *full* map. -/

section RqsWalk

variable {D₀ D : Type*} (G₀ : Hypermap D₀) (G : Hypermap D) (h : D → D₀)

/-- The images under `h` of the darts `p` fit the ring questions `qs`: each
question fits at the node of the image of the corresponding dart, and that
image has the arity of the dart increased by the question's outer arity. -/
def rqsFit : List RingQuestion → List D → Prop
  | [], [] => True
  | rq :: qs, x :: p =>
      G₀.arity (h x) = rq.outerArity + G.arity x ∧
        G₀.Fitq (G₀.node (h x)) rq.question ∧ rqsFit qs p
  | _, _ => False

@[simp] theorem rqsFit_nil_nil : rqsFit G₀ G h [] [] := trivial

@[simp] theorem rqsFit_cons (rq : RingQuestion) (qs : List RingQuestion) (x : D)
    (p : List D) :
    rqsFit G₀ G h (rq :: qs) (x :: p) ↔
      (G₀.arity (h x) = rq.outerArity + G.arity x ∧
        G₀.Fitq (G₀.node (h x)) rq.question ∧ rqsFit G₀ G h qs p) := Iff.rfl

@[simp] theorem not_rqsFit_nil_cons (x : D) (p : List D) :
    ¬ rqsFit G₀ G h [] (x :: p) := id

@[simp] theorem not_rqsFit_cons_nil (rq : RingQuestion) (qs : List RingQuestion) :
    ¬ rqsFit G₀ G h (rq :: qs) [] := id

/-- A list of ring questions fits exactly as many darts as it has entries. -/
theorem length_eq_of_rqsFit : ∀ {qs : List RingQuestion} {p : List D},
    rqsFit G₀ G h qs p → qs.length = p.length := by
  intro qs
  induction qs with
  | nil => intro p hp; cases p with
    | nil => rfl
    | cons _ _ => exact absurd hp (not_rqsFit_nil_cons G₀ G h _ _)
  | cons rq qs ih =>
    intro p hp
    cases p with
    | nil => exact absurd hp (not_rqsFit_cons_nil G₀ G h _ _)
    | cons x p => simpa using ih hp.2.2

/-- The darts a list of ring questions visits, starting from the darts `p` of
the ring of the intermediate map: a kernel dart is visited itself, and then the
question rooted at its node is walked. -/
def rqsWalk : List RingQuestion → List D₀ → List D₀
  | rq :: qs, u :: p =>
      (if rq.isKernel then [u] else []) ++
        (G₀.walkq (G₀.node u) rq.question ++ rqsWalk qs p)
  | _, _ => []

@[simp] theorem rqsWalk_nil_left (p : List D₀) : rqsWalk G₀ [] p = [] := by
  cases p <;> rfl

@[simp] theorem rqsWalk_nil_right (qs : List RingQuestion) : rqsWalk G₀ qs [] = [] := by
  cases qs <;> rfl

@[simp] theorem rqsWalk_cons (rq : RingQuestion) (qs : List RingQuestion) (u : D₀)
    (p : List D₀) :
    rqsWalk G₀ (rq :: qs) (u :: p) =
      (if rq.isKernel then [u] else []) ++
        (G₀.walkq (G₀.node u) rq.question ++ rqsWalk G₀ qs p) := rfl

/-- Fitting splits along a concatenation of the ring. -/
theorem rqsFit_append : ∀ {qs₁ : List RingQuestion} {p₁ : List D}
    (qs₂ : List RingQuestion) (p₂ : List D), qs₁.length = p₁.length →
    (rqsFit G₀ G h (qs₁ ++ qs₂) (p₁ ++ p₂) ↔
      rqsFit G₀ G h qs₁ p₁ ∧ rqsFit G₀ G h qs₂ p₂) := by
  intro qs₁
  induction qs₁ with
  | nil =>
    intro p₁ qs₂ p₂ hlen
    cases p₁ with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons rq qs ih =>
    intro p₁ qs₂ p₂ hlen
    cases p₁ with
    | nil => simp at hlen
    | cons x p =>
      simp only [List.cons_append, rqsFit_cons, ih qs₂ p₂ (by simpa using hlen)]
      tauto

/-- The walk splits along a concatenation of the ring. -/
theorem rqsWalk_append : ∀ {qs₁ : List RingQuestion} {p₁ : List D₀}
    (qs₂ : List RingQuestion) (p₂ : List D₀), qs₁.length = p₁.length →
    rqsWalk G₀ (qs₁ ++ qs₂) (p₁ ++ p₂) = rqsWalk G₀ qs₁ p₁ ++ rqsWalk G₀ qs₂ p₂ := by
  intro qs₁
  induction qs₁ with
  | nil =>
    intro p₁ qs₂ p₂ hlen
    cases p₁ with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons rq qs ih =>
    intro p₁ qs₂ p₂ hlen
    cases p₁ with
    | nil => simp at hlen
    | cons u p =>
      simp only [List.cons_append, rqsWalk_cons, ih qs₂ p₂ (by simpa using hlen),
        List.append_assoc]

/-- Rotating the ring and the ring questions together preserves fitting.  This
is the `R n` step of the compilation. -/
theorem rqsFit_rotate {qs : List RingQuestion} {p : List D} (n : ℕ)
    (hfit : rqsFit G₀ G h qs p) : rqsFit G₀ G h (qs.rotate n) (p.rotate n) := by
  have hlen : qs.length = p.length := length_eq_of_rqsFit G₀ G h hfit
  rcases Nat.eq_zero_or_pos qs.length with h0 | hpos
  · have hq : qs = [] := List.eq_nil_of_length_eq_zero h0
    have hp : p = [] := List.eq_nil_of_length_eq_zero (hlen ▸ h0)
    subst hq
    subst hp
    simp
  · have hm : n % qs.length ≤ qs.length := (Nat.mod_lt _ hpos).le
    have hm2 : n % qs.length ≤ p.length := hlen ▸ hm
    have hqr : qs.rotate n = qs.drop (n % qs.length) ++ qs.take (n % qs.length) := by
      rw [← List.rotate_mod qs n, List.rotate_eq_drop_append_take hm]
    have hpr : p.rotate n = p.drop (n % qs.length) ++ p.take (n % qs.length) := by
      conv_lhs => rw [← List.rotate_mod p n, ← hlen]
      rw [List.rotate_eq_drop_append_take hm2]
    have hsplit : rqsFit G₀ G h (qs.take (n % qs.length) ++ qs.drop (n % qs.length))
        (p.take (n % qs.length) ++ p.drop (n % qs.length)) := by
      rw [List.take_append_drop, List.take_append_drop]
      exact hfit
    obtain ⟨h1, h2⟩ := (rqsFit_append G₀ G h _ _ (by simp [hlen])).mp hsplit
    rw [hqr, hpr]
    exact (rqsFit_append G₀ G h _ _ (by simp [hlen])).mpr ⟨h2, h1⟩

/-- Rotating the ring and the ring questions together permutes the darts the
questions visit. -/
theorem rqsWalk_rotate {qs : List RingQuestion} {p : List D₀}
    (hlen : qs.length = p.length) (n : ℕ) :
    (rqsWalk G₀ (qs.rotate n) (p.rotate n)).Perm (rqsWalk G₀ qs p) := by
  rcases Nat.eq_zero_or_pos qs.length with h0 | hpos
  · have hq : qs = [] := List.eq_nil_of_length_eq_zero h0
    have hp : p = [] := List.eq_nil_of_length_eq_zero (hlen ▸ h0)
    subst hq
    subst hp
    simp
  · have hm : n % qs.length ≤ qs.length := (Nat.mod_lt _ hpos).le
    have hm2 : n % qs.length ≤ p.length := hlen ▸ hm
    have hqr : qs.rotate n = qs.drop (n % qs.length) ++ qs.take (n % qs.length) := by
      rw [← List.rotate_mod qs n, List.rotate_eq_drop_append_take hm]
    have hpr : p.rotate n = p.drop (n % qs.length) ++ p.take (n % qs.length) := by
      conv_lhs => rw [← List.rotate_mod p n, ← hlen]
      rw [List.rotate_eq_drop_append_take hm2]
    rw [hqr, hpr, rqsWalk_append G₀ _ _ (by simp [hlen])]
    refine List.Perm.trans List.perm_append_comm ?_
    rw [← rqsWalk_append G₀ _ _ (by simp [hlen]), List.take_append_drop,
      List.take_append_drop]

/-- The invariant of the compilation: the ring questions `qs` fit the ring `r`
of the intermediate map, the faces of the full map that are neither in the
image of `h` nor along `r` have a good ring arity, and the darts visited by
`qs` together with the ring `r₀` of the full map form a transversal of exactly
those faces that are outside the image of `h` or meet `r`. -/
structure RqsProper (r₀ : List D₀) (r : List D) (qs : List RingQuestion) : Prop where
  /-- The questions fit the ring of the intermediate map. -/
  fit : rqsFit G₀ G h qs r
  /-- The ring faces of the full map not yet covered have a good arity. -/
  ringArity : ∀ u ∈ r₀, u ∉ Set.range h → ¬ G₀.Fband (r.map h) u → G₀.GoodRingArity u
  /-- The darts visited meet pairwise distinct faces. -/
  simple : G₀.Simple (rqsWalk G₀ qs (r.map h) ++ r₀)
  /-- The faces met are exactly those outside the image of `h`, or on `r`. -/
  cover : ∀ u, G₀.Fband (rqsWalk G₀ qs (r.map h) ++ r₀) u ↔
    (u ∉ Set.range h ∨ G₀.Fband (r.map h) u)

end RqsWalk

/-! ### The arities of the faces of a construction step

The compiler computes arities, so it must know how a step changes them.  A `Y`
step splices its two new darts into the faces of `node x₀` and of `x₀`, an `H`
step splices a third one into the face of `node⁻¹ x₀`, and all the other faces
keep their arity. -/

/-- The arity of a dart is the length of any duplicate-free list of exactly the
darts of its face. -/
private theorem arity_eq_length {D : Type*} [Finite D] {G : Hypermap D} {x : D}
    {L : List D} (hnd : L.Nodup) (hmem : ∀ y, y ∈ L ↔ G.CFace x y) :
    G.arity x = L.length := by
  classical
  have h1 := ((nodup_orbitList G.face x).subperm
    fun a ha => (hmem a).mpr (mem_orbitList.mp ha)).length_le
  have h2 := (hnd.subperm fun a ha => mem_orbitList.mpr ((hmem a).mp ha)).length_le
  rw [length_orbitList] at h1 h2
  have harity : G.arity x = Function.minimalPeriod G.face x := rfl
  omega

/-- **The face of an old dart after a `Y` step**: besides the images of the old
face, the face of `x₀` acquires the dart `Xe` and the face of `node x₀` the dart
`icp Xe`. -/
private theorem cface_ecpY_icpY (M : PointedMap) (hp : M.Proper) (x : M.Dart)
    (v : EcpDart (EcpDart M.Dart)) :
    M.ecpY.map.CFace (M.icpY x) v ↔
      (∃ y : M.Dart, M.map.CFace x y ∧ v = M.icpY y)
        ∨ (v = .icp .Xe ∧ M.map.CFace x (M.map.node M.point))
        ∨ (v = .Xe ∧ M.map.CFace x M.point) := by
  have hXe : M.ecpY.map.CFace (.Xe : M.ecpY.Dart) (M.icpY M.point) :=
    Hypermap.cface_Xe_ecpY M.map M.point hp
  have hiXe : M.ecpY.map.CFace (.icp .Xe : M.ecpY.Dart) (M.icpY (M.map.node M.point)) :=
    Hypermap.cface_icpXe_ecpY M.map M.point
  cases v with
  | X =>
    constructor
    · intro hc
      exact absurd hc.symm (PointedMap.not_cface_ecpY_icpY M x)
    · rintro (⟨y, -, hy⟩ | ⟨hy, -⟩ | ⟨hy, -⟩)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart M.Dart)) = .icp (.icp y) from hy)
            (by simp)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart M.Dart)) = .icp .Xe from hy)
            (by simp)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart M.Dart)) = .Xe from hy)
            (by simp)
  | Xe =>
    constructor
    · intro hc
      exact Or.inr (Or.inr ⟨rfl, (PointedMap.cface_icpY' M x M.point).mp (hc.trans hXe)⟩)
    · rintro (⟨y, -, hy⟩ | ⟨hy, -⟩ | ⟨-, hy⟩)
      · exact absurd (show (EcpDart.Xe : EcpDart (EcpDart M.Dart)) = .icp (.icp y) from hy)
            (by simp)
      · exact absurd (show (EcpDart.Xe : EcpDart (EcpDart M.Dart)) = .icp .Xe from hy)
            (by simp)
      · exact ((PointedMap.cface_icpY' M x M.point).mpr hy).trans hXe.symm
  | icp w =>
    cases w with
    | X =>
      constructor
      · intro hc
        exact absurd ((Hypermap.cface_icpN M.ecpU.map .X (.icp x) .X).mp hc)
          (fun hcc => absurd ((Hypermap.cface_ecpU M.map M.point _).mp hcc.symm) (by simp))
      · rintro (⟨y, -, hy⟩ | ⟨hy, -⟩ | ⟨hy, -⟩)
        · exact absurd (show (EcpDart.icp .X : EcpDart (EcpDart M.Dart)) = .icp (.icp y) from hy)
              (by simp)
        · exact absurd (show (EcpDart.icp .X : EcpDart (EcpDart M.Dart)) = .icp .Xe from hy)
              (by simp)
        · exact absurd (show (EcpDart.icp .X : EcpDart (EcpDart M.Dart)) = .Xe from hy)
              (by simp)
    | Xe =>
      constructor
      · intro hc
        exact Or.inr (Or.inl ⟨rfl,
          (PointedMap.cface_icpY' M x (M.map.node M.point)).mp (hc.trans hiXe)⟩)
      · rintro (⟨y, -, hy⟩ | ⟨-, hy⟩ | ⟨hy, -⟩)
        · exact absurd (show (EcpDart.icp .Xe : EcpDart (EcpDart M.Dart)) = .icp (.icp y) from hy)
              (by simp)
        · exact ((PointedMap.cface_icpY' M x (M.map.node M.point)).mpr hy).trans hiXe.symm
        · exact absurd (show (EcpDart.icp .Xe : EcpDart (EcpDart M.Dart)) = .Xe from hy)
              (by simp)
    | icp y =>
      constructor
      · intro hc
        exact Or.inl ⟨y, (PointedMap.cface_icpY' M x y).mp hc, rfl⟩
      · rintro (⟨z, hz, hy⟩ | ⟨hy, -⟩ | ⟨hy, -⟩)
        · have hzy : y = z := by
            have hy' : (EcpDart.icp (EcpDart.icp y) : EcpDart (EcpDart M.Dart))
                = .icp (.icp z) := hy
            simpa using hy'
          exact (PointedMap.cface_icpY' M x y).mpr (hzy ▸ hz)
        · exact absurd (show (EcpDart.icp (.icp y) : EcpDart (EcpDart M.Dart)) = .icp .Xe from hy)
              (by simp)
        · exact absurd (show (EcpDart.icp (.icp y) : EcpDart (EcpDart M.Dart)) = .Xe from hy)
              (by simp)

/-- **The face of an old dart after an `H` step**: an `H` step is a `Y` step
followed by an `N` step, which splices one more dart into the face of
`node⁻¹ x₀`. -/
private theorem cface_ecpH_icpH (M : PointedMap) (hp : M.Proper) (x : M.Dart)
    (v : EcpDart (EcpDart (EcpDart M.Dart))) :
    M.ecpH.map.CFace (M.icpH x) v ↔
      (∃ y : M.Dart, M.map.CFace x y ∧ v = M.icpH y)
        ∨ (v = .icp (.icp .Xe) ∧ M.map.CFace x (M.map.node M.point))
        ∨ (v = .icp .Xe ∧ M.map.CFace x M.point)
        ∨ (v = .Xe ∧ M.map.CFace x (M.map.node⁻¹ M.point)) := by
  have hstep : ∀ w : EcpDart (EcpDart M.Dart),
      M.ecpH.map.CFace (M.icpH x) (.icp w) ↔ M.ecpY.map.CFace (M.icpY x) w :=
    fun w => Hypermap.cface_icpN M.ecpY.map .X (.icp (.icp x)) w
  cases v with
  | X =>
    have hX : M.ecpH.map.CFace (.X : M.ecpH.Dart) (M.icpH x)
        ↔ M.ecpY.map.CFace (M.icpY x) .X :=
      Hypermap.cface_ecpN_icp M.ecpY.map .X (.icp (.icp x))
    constructor
    · intro hc
      rcases (cface_ecpY_icpY M hp x .X).mp (hX.mp hc.symm) with
        ⟨y, -, hy⟩ | ⟨hy, -⟩ | ⟨hy, -⟩
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart M.Dart)) = .icp (.icp y) from hy)
            (by simp)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart M.Dart)) = .icp .Xe from hy)
            (by simp)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart M.Dart)) = .Xe from hy)
            (by simp)
    · rintro (⟨y, -, hy⟩ | ⟨hy, -⟩ | ⟨hy, -⟩ | ⟨hy, -⟩)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart (EcpDart M.Dart)))
            = .icp (.icp (.icp y)) from hy) (by simp)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart (EcpDart M.Dart)))
            = .icp (.icp .Xe) from hy) (by simp)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart (EcpDart M.Dart))) = .icp .Xe from hy)
            (by simp)
      · exact absurd (show (EcpDart.X : EcpDart (EcpDart (EcpDart M.Dart))) = .Xe from hy)
            (by simp)
  | Xe =>
    have hXe : M.ecpH.map.CFace (.Xe : M.ecpH.Dart) (M.icpH x)
        ↔ M.ecpY.map.CFace (M.icpY x) (M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ .X)) :=
      Hypermap.cface_Xe_icpN M.ecpY.map .X (.icp (.icp x))
    have hb2 : M.ecpY.map.CFace (M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ .X))
        (M.icpY (M.map.node⁻¹ M.point)) := Hypermap.cface_b2_ecpY M.map M.point hp
    constructor
    · intro hc
      exact Or.inr (Or.inr (Or.inr ⟨rfl,
        (PointedMap.cface_icpY' M x _).mp ((hXe.mp hc.symm).trans hb2)⟩))
    · rintro (⟨y, -, hy⟩ | ⟨hy, -⟩ | ⟨hy, -⟩ | ⟨-, hy⟩)
      · exact absurd (show (EcpDart.Xe : EcpDart (EcpDart (EcpDart M.Dart)))
            = .icp (.icp (.icp y)) from hy) (by simp)
      · exact absurd (show (EcpDart.Xe : EcpDart (EcpDart (EcpDart M.Dart)))
            = .icp (.icp .Xe) from hy) (by simp)
      · exact absurd (show (EcpDart.Xe : EcpDart (EcpDart (EcpDart M.Dart))) = .icp .Xe from hy)
            (by simp)
      · exact (hXe.mpr (((PointedMap.cface_icpY' M x _).mpr hy).trans hb2.symm)).symm
  | icp w =>
    refine ((hstep w).trans (cface_ecpY_icpY M hp x w)).trans ?_
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨rfl, hy⟩ | ⟨rfl, hy⟩)
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, hy⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hy⟩))
    · rintro (⟨y, hy, hv⟩ | ⟨hv, hy⟩ | ⟨hv, hy⟩ | ⟨hv, -⟩)
      · refine Or.inl ⟨y, hy, ?_⟩
        have hv' : (EcpDart.icp w : EcpDart (EcpDart (EcpDart M.Dart)))
            = .icp (.icp (.icp y)) := hv
        injection hv'
      · refine Or.inr (Or.inl ⟨?_, hy⟩)
        have hv' : (EcpDart.icp w : EcpDart (EcpDart (EcpDart M.Dart)))
            = .icp (.icp .Xe) := hv
        injection hv'
      · refine Or.inr (Or.inr ⟨?_, hy⟩)
        have hv' : (EcpDart.icp w : EcpDart (EcpDart (EcpDart M.Dart))) = .icp .Xe := hv
        injection hv'
      · exact absurd (show (EcpDart.icp w : EcpDart (EcpDart (EcpDart M.Dart))) = .Xe from hv)
            (by simp)

/-- The arity of an old face after a `U` step, given the list `E` of the darts
the step adds to it. -/
private theorem arity_icpU_aux {D : Type} [Finite D] [DecidableEq D] (G : Hypermap D)
    (x₀ x : D) (E : List (EcpDart D)) (hEnd : E.Nodup)
    (hE : ∀ v, v ∈ E ↔ (v = .Xe ∧ G.CFace x (G.node x₀))) :
    (Hypermap.ecpUMap G x₀).arity (.icp x) = G.arity x + E.length := by
  set L : List (EcpDart D) := (orbitList G.face x).map .icp ++ E with hL
  have hlen : L.length = G.arity x + E.length := by
    rw [hL, List.length_append, List.length_map, length_orbitList]
    rfl
  have hnd : L.Nodup := by
    rw [hL]
    refine List.nodup_append.mpr
      ⟨List.Nodup.map EcpDart.icp_injective (nodup_orbitList _ _), hEnd, ?_⟩
    intro a ha b hb
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨rfl, -⟩ := (hE b).mp hb
    simp
  have hmem : ∀ v, v ∈ L ↔ (Hypermap.ecpUMap G x₀).CFace (.icp x) v := by
    intro v
    rw [hL, List.mem_append, hE v]
    cases v with
    | X =>
      constructor
      · rintro (hv | ⟨hv, -⟩)
        · obtain ⟨y, -, hy⟩ := List.mem_map.mp hv
          exact absurd hy (by simp)
        · exact absurd hv (by simp)
      · intro hc
        exact absurd ((Hypermap.cface_ecpU G x₀ _).mp hc.symm) (by simp)
    | Xe =>
      constructor
      · rintro (hv | ⟨-, hc⟩)
        · obtain ⟨y, -, hy⟩ := List.mem_map.mp hv
          exact absurd hy (by simp)
        · exact ((Hypermap.cface_Xe_icpU G x₀ x).mpr hc).symm
      · intro hc
        exact Or.inr ⟨rfl, (Hypermap.cface_Xe_icpU G x₀ x).mp hc.symm⟩
    | icp y =>
      constructor
      · rintro (hv | ⟨hv, -⟩)
        · obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hv
          have hzy' : z = y := EcpDart.icp_injective hzy
          exact (Hypermap.cface_icpU G x₀ x y).mpr (hzy' ▸ mem_orbitList.mp hz)
        · exact absurd hv (by simp)
      · intro hc
        exact Or.inl (List.mem_map.mpr
          ⟨y, mem_orbitList.mpr ((Hypermap.cface_icpU G x₀ x y).mp hc), rfl⟩)
  rw [arity_eq_length (G := Hypermap.ecpUMap G x₀) hnd hmem, hlen]

/-- The arity of an old face after an `N` step, given the list `E` of the darts
the step adds to it. -/
private theorem arity_icpN_aux {D : Type} [Finite D] [DecidableEq D] (G : Hypermap D)
    (x₀ x : D) (E : List (EcpDart D)) (hEnd : E.Nodup)
    (hE : ∀ v, v ∈ E ↔ ((v = .X ∧ G.CFace x x₀)
                        ∨ (v = .Xe ∧ G.CFace x (G.node⁻¹ (G.node⁻¹ x₀))))) :
    (Hypermap.ecpNMap G x₀).arity (.icp x) = G.arity x + E.length := by
  set L : List (EcpDart D) := (orbitList G.face x).map .icp ++ E with hL
  have hlen : L.length = G.arity x + E.length := by
    rw [hL, List.length_append, List.length_map, length_orbitList]
    rfl
  have hnd : L.Nodup := by
    rw [hL]
    refine List.nodup_append.mpr
      ⟨List.Nodup.map EcpDart.icp_injective (nodup_orbitList _ _), hEnd, ?_⟩
    intro a ha b hb
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha
    rcases (hE b).mp hb with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hmem : ∀ v, v ∈ L ↔ (Hypermap.ecpNMap G x₀).CFace (.icp x) v := by
    intro v
    rw [hL, List.mem_append, hE v]
    cases v with
    | X =>
      constructor
      · rintro (hv | ⟨-, hc⟩ | ⟨hv, -⟩)
        · obtain ⟨y, -, hy⟩ := List.mem_map.mp hv
          exact absurd hy (by simp)
        · exact ((Hypermap.cface_ecpN_icp G x₀ x).mpr hc).symm
        · exact absurd hv (by simp)
      · intro hc
        exact Or.inr (Or.inl ⟨rfl, (Hypermap.cface_ecpN_icp G x₀ x).mp hc.symm⟩)
    | Xe =>
      constructor
      · rintro (hv | ⟨hv, -⟩ | ⟨-, hc⟩)
        · obtain ⟨y, -, hy⟩ := List.mem_map.mp hv
          exact absurd hy (by simp)
        · exact absurd hv (by simp)
        · exact ((Hypermap.cface_Xe_icpN G x₀ x).mpr hc).symm
      · intro hc
        exact Or.inr (Or.inr ⟨rfl, (Hypermap.cface_Xe_icpN G x₀ x).mp hc.symm⟩)
    | icp y =>
      constructor
      · rintro (hv | ⟨hv, -⟩ | ⟨hv, -⟩)
        · obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hv
          have hzy' : z = y := EcpDart.icp_injective hzy
          exact (Hypermap.cface_icpN G x₀ x y).mpr (hzy' ▸ mem_orbitList.mp hz)
        · exact absurd hv (by simp)
        · exact absurd hv (by simp)
      · intro hc
        exact Or.inl (List.mem_map.mpr
          ⟨y, mem_orbitList.mpr ((Hypermap.cface_icpN G x₀ x y).mp hc), rfl⟩)
  rw [arity_eq_length (G := Hypermap.ecpNMap G x₀) hnd hmem, hlen]

/-- The new face of a `U` step has a single dart. -/
private theorem arity_ecpU_X {D : Type} [Finite D] [DecidableEq D] (G : Hypermap D) (x₀ : D) :
    (Hypermap.ecpUMap G x₀).arity .X = 1 := by
  have hmem : ∀ y : EcpDart D, y ∈ ([.X] : List (EcpDart D))
      ↔ (Hypermap.ecpUMap G x₀).CFace .X y := by
    intro y
    rw [Hypermap.cface_ecpU G x₀ y]
    simp
  exact arity_eq_length (G := Hypermap.ecpUMap G x₀) (List.nodup_singleton _) hmem

/-- The face of `x₀` seen two node steps back from the new dart of a `U` step. -/
private theorem node_inv2_ecpU (M : PointedMap) (hp : M.Proper) :
    (Hypermap.ecpUMap M.map M.point).node⁻¹
      ((Hypermap.ecpUMap M.map M.point).node⁻¹ .X) = .icp M.point := by
  rw [Hypermap.node_inv_ecpU_X, Hypermap.node_inv_ecpU_icp_node M.map M.point hp]

/-- **The arity of an old face after a `Y` step**, from the lists of darts the
two new darts contribute to it. -/
private theorem arity_icpY_gen (M : PointedMap) (hp : M.Proper) (x : M.Dart)
    (E₁ : List (EcpDart M.Dart)) (hnd₁ : E₁.Nodup)
    (hE₁ : ∀ v, v ∈ E₁ ↔ (v = .Xe ∧ M.map.CFace x (M.map.node M.point)))
    (E₂ : List (EcpDart (EcpDart M.Dart))) (hnd₂ : E₂.Nodup)
    (hE₂ : ∀ v, v ∈ E₂ ↔ (v = .Xe ∧ M.map.CFace x M.point)) :
    M.ecpY.map.arity (M.icpY x) = M.map.arity x + E₁.length + E₂.length := by
  have hU := arity_icpU_aux M.map M.point x E₁ hnd₁ hE₁
  have hnn := node_inv2_ecpU M hp
  have hN := arity_icpN_aux (Hypermap.ecpUMap M.map M.point) .X (.icp x) E₂ hnd₂ (by
    intro v
    rw [hE₂ v]
    constructor
    · rintro ⟨rfl, hc⟩
      refine Or.inr ⟨rfl, ?_⟩
      rw [hnn]
      exact (Hypermap.cface_icpU M.map M.point x M.point).mpr hc
    · rintro (⟨rfl, hc⟩ | ⟨rfl, hc⟩)
      · exact absurd ((Hypermap.cface_ecpU M.map M.point _).mp hc.symm) (by simp)
      · rw [hnn] at hc
        exact ⟨rfl, (Hypermap.cface_icpU M.map M.point x M.point).mp hc⟩)
  have heq : M.ecpY.map.arity (M.icpY x)
      = (Hypermap.ecpUMap M.map M.point).arity (.icp x) + E₂.length := hN
  rw [heq, hU]

/-- A `Y` step leaves the arity of a face away from `x₀` and `node x₀`. -/
private theorem arity_icpY_of_not (M : PointedMap) (hp : M.Proper) {x : M.Dart}
    (h1 : ¬ M.map.CFace x (M.map.node M.point)) (h2 : ¬ M.map.CFace x M.point) :
    M.ecpY.map.arity (M.icpY x) = M.map.arity x := by
  have h := arity_icpY_gen M hp x [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h1 hc.2)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h2 hc.2)
  simpa using h

/-- A `Y` step adds one dart to the face of `node x₀`. -/
private theorem arity_icpY_of_node (M : PointedMap) (hp : M.Proper) {x : M.Dart}
    (h1 : M.map.CFace x (M.map.node M.point)) (h2 : ¬ M.map.CFace x M.point) :
    M.ecpY.map.arity (M.icpY x) = M.map.arity x + 1 := by
  have h := arity_icpY_gen M hp x [.Xe] (List.nodup_singleton _)
    (by intro v; simp only [List.mem_singleton]; exact ⟨fun hv => ⟨hv, h1⟩, fun hv => hv.1⟩)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h2 hc.2)
  simpa using h

/-- A `Y` step adds one dart to the face of `x₀`. -/
private theorem arity_icpY_of_point (M : PointedMap) (hp : M.Proper) {x : M.Dart}
    (h1 : ¬ M.map.CFace x (M.map.node M.point)) (h2 : M.map.CFace x M.point) :
    M.ecpY.map.arity (M.icpY x) = M.map.arity x + 1 := by
  have h := arity_icpY_gen M hp x [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h1 hc.2)
    [.Xe] (List.nodup_singleton _)
    (by intro v; simp only [List.mem_singleton]; exact ⟨fun hv => ⟨hv, h2⟩, fun hv => hv.1⟩)
  simpa using h

/-- The new face of a `Y` step has two darts. -/
private theorem arity_ecpY_X (M : PointedMap) (hp : M.Proper) :
    M.ecpY.map.arity (.X : M.ecpY.Dart) = 2 := by
  have hnn := node_inv2_ecpU M hp
  have hN := arity_icpN_aux (Hypermap.ecpUMap M.map M.point) .X .X [.X]
    (List.nodup_singleton _) (by
      intro v
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        exact Or.inl ⟨rfl, Equiv.Perm.SameCycle.refl _ _⟩
      · rintro (⟨hv, -⟩ | ⟨rfl, hc⟩)
        · exact hv
        · rw [hnn] at hc
          exact absurd ((Hypermap.cface_ecpU M.map M.point _).mp hc) (by simp))
  rw [arity_ecpU_X] at hN
  exact (Hypermap.arity_cface _
    (Hypermap.cface_ecpN (Hypermap.ecpUMap M.map M.point) .X)).trans hN

/-- **The arity of an old face after an `H` step**, from the lists of darts the
three new darts contribute to it. -/
private theorem arity_icpH_gen (M : PointedMap) (hp : M.Proper) (x : M.Dart)
    (E₁ : List (EcpDart M.Dart)) (hnd₁ : E₁.Nodup)
    (hE₁ : ∀ v, v ∈ E₁ ↔ (v = .Xe ∧ M.map.CFace x (M.map.node M.point)))
    (E₂ : List (EcpDart (EcpDart M.Dart))) (hnd₂ : E₂.Nodup)
    (hE₂ : ∀ v, v ∈ E₂ ↔ (v = .Xe ∧ M.map.CFace x M.point))
    (E₃ : List (EcpDart M.ecpY.Dart)) (hnd₃ : E₃.Nodup)
    (hE₃ : ∀ v, v ∈ E₃ ↔ (v = .Xe ∧ M.map.CFace x (M.map.node⁻¹ M.point))) :
    M.ecpH.map.arity (M.icpH x)
      = M.map.arity x + E₁.length + E₂.length + E₃.length := by
  have hY := arity_icpY_gen M hp x E₁ hnd₁ hE₁ E₂ hnd₂ hE₂
  have hb2 : M.ecpY.map.CFace (M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ .X))
      (M.icpY (M.map.node⁻¹ M.point)) := Hypermap.cface_b2_ecpY M.map M.point hp
  have hN := arity_icpN_aux M.ecpY.map .X (.icp (.icp x)) E₃ hnd₃ (by
    intro v
    rw [hE₃ v]
    constructor
    · rintro ⟨rfl, hc⟩
      refine Or.inr ⟨rfl, ?_⟩
      exact ((PointedMap.cface_icpY' M x (M.map.node⁻¹ M.point)).mpr hc).trans hb2.symm
    · rintro (⟨rfl, hc⟩ | ⟨rfl, hc⟩)
      · exact absurd hc.symm (PointedMap.not_cface_ecpY_icpY M x)
      · exact ⟨rfl, (PointedMap.cface_icpY' M x (M.map.node⁻¹ M.point)).mp (hc.trans hb2)⟩)
  have heq : M.ecpH.map.arity (M.icpH x)
      = M.ecpY.map.arity (M.icpY x) + E₃.length := hN
  rw [heq, hY]

/-- An `H` step leaves the arity of a face away from `x₀`, `node x₀` and
`node⁻¹ x₀`. -/
private theorem arity_icpH_of_not (M : PointedMap) (hp : M.Proper) {x : M.Dart}
    (h1 : ¬ M.map.CFace x (M.map.node M.point)) (h2 : ¬ M.map.CFace x M.point)
    (h3 : ¬ M.map.CFace x (M.map.node⁻¹ M.point)) :
    M.ecpH.map.arity (M.icpH x) = M.map.arity x := by
  have h := arity_icpH_gen M hp x [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h1 hc.2)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h2 hc.2)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h3 hc.2)
  simpa using h

/-- An `H` step adds one dart to the face of `node x₀`. -/
private theorem arity_icpH_of_node (M : PointedMap) (hp : M.Proper) {x : M.Dart}
    (h1 : M.map.CFace x (M.map.node M.point)) (h2 : ¬ M.map.CFace x M.point)
    (h3 : ¬ M.map.CFace x (M.map.node⁻¹ M.point)) :
    M.ecpH.map.arity (M.icpH x) = M.map.arity x + 1 := by
  have h := arity_icpH_gen M hp x [.Xe] (List.nodup_singleton _)
    (by intro v; simp only [List.mem_singleton]; exact ⟨fun hv => ⟨hv, h1⟩, fun hv => hv.1⟩)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h2 hc.2)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h3 hc.2)
  simpa using h

/-- An `H` step adds one dart to the face of `x₀`. -/
private theorem arity_icpH_of_point (M : PointedMap) (hp : M.Proper) {x : M.Dart}
    (h1 : ¬ M.map.CFace x (M.map.node M.point)) (h2 : M.map.CFace x M.point)
    (h3 : ¬ M.map.CFace x (M.map.node⁻¹ M.point)) :
    M.ecpH.map.arity (M.icpH x) = M.map.arity x + 1 := by
  have h := arity_icpH_gen M hp x [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h1 hc.2)
    [.Xe] (List.nodup_singleton _)
    (by intro v; simp only [List.mem_singleton]; exact ⟨fun hv => ⟨hv, h2⟩, fun hv => hv.1⟩)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h3 hc.2)
  simpa using h

/-- An `H` step adds one dart to the face of `node⁻¹ x₀`. -/
private theorem arity_icpH_of_node_inv (M : PointedMap) (hp : M.Proper) {x : M.Dart}
    (h1 : ¬ M.map.CFace x (M.map.node M.point)) (h2 : ¬ M.map.CFace x M.point)
    (h3 : M.map.CFace x (M.map.node⁻¹ M.point)) :
    M.ecpH.map.arity (M.icpH x) = M.map.arity x + 1 := by
  have h := arity_icpH_gen M hp x [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h1 hc.2)
    [] List.nodup_nil
    (by intro v; simp only [List.not_mem_nil, false_iff]; exact fun hc => h2 hc.2)
    [.Xe] (List.nodup_singleton _)
    (by intro v; simp only [List.mem_singleton]; exact ⟨fun hv => ⟨hv, h3⟩, fun hv => hv.1⟩)
  simpa using h

/-- The new face of an `H` step has three darts. -/
private theorem arity_ecpH_X (M : PointedMap) (hp : M.Proper) :
    M.ecpH.map.arity (.X : M.ecpH.Dart) = 3 := by
  have hb2 : M.ecpY.map.CFace (M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ .X))
      (M.icpY (M.map.node⁻¹ M.point)) := Hypermap.cface_b2_ecpY M.map M.point hp
  have hN := arity_icpN_aux M.ecpY.map .X .X [.X] (List.nodup_singleton _) (by
    intro v
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact Or.inl ⟨rfl, Equiv.Perm.SameCycle.refl _ _⟩
    · rintro (⟨hv, -⟩ | ⟨rfl, hc⟩)
      · exact hv
      · exact absurd (hc.trans hb2) (PointedMap.not_cface_ecpY_icpY M _))
  rw [arity_ecpY_X M hp] at hN
  exact (Hypermap.arity_cface _ (Hypermap.cface_ecpN M.ecpY.map .X)).trans hN

/-- A dart of a face-simple list is on no face of the rest of the list. -/
private theorem not_cface_of_simple_cons {D : Type*} {G : Hypermap D} {a : D} {p : List D}
    (h : G.Simple (a :: p)) {x : D} (hx : x ∈ p) : ¬ G.CFace x a :=
  fun hc => h.not_fband ⟨x, hx, hc.symm⟩

/-! ### The compiler is correct

The invariant `RqsProper` is carried through the program, one step at a time;
when the program is exhausted the two remaining ring questions are read off as
a valid quiz for the ring of the full map. -/

/-- Rotating a list forward by `n` and back by `n` modulo its length. -/
private theorem rotate_rotate_sub_mod {α : Type*} (l : List α) (n : ℕ) :
    (l.rotate n).rotate (l.length - n % l.length) = l := by
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · have hl : l = [] := List.eq_nil_of_length_eq_zero h0
    subst hl
    simp
  · rw [List.rotate_rotate]
    have hmod : n % l.length < l.length := Nat.mod_lt _ hpos
    have hd : l.length * (n / l.length) + n % l.length = n := Nat.div_add_mod n l.length
    have hkey : n + (l.length - n % l.length) = l.length * (n / l.length + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hkey]
    exact List.rotate_length_mul l _

/-- The face band only depends on the darts of a list. -/
private theorem fband_perm {D : Type*} {G : Hypermap D} {p q : List D} (hpq : p.Perm q)
    (x : D) : G.Fband p x ↔ G.Fband q x :=
  ⟨fun ⟨y, hy, hx⟩ => ⟨y, hpq.mem_iff.mp hy, hx⟩,
   fun ⟨y, hy, hx⟩ => ⟨y, hpq.mem_iff.mpr hy, hx⟩⟩

/-- **An `R` step preserves the invariant**: the ring and the ring questions
rotate together. -/
theorem rqsProper_R {D₀ : Type*} (G₀ : Hypermap D₀) (r₀ : List D₀) (n : ℕ)
    (cp : CProg) (h : (cpmap cp).Dart → D₀) (qs : List RingQuestion)
    (hq : RqsProper G₀ (cpmap cp).map h r₀ ((cpmap cp).cpring.rotate n) qs) :
    RqsProper G₀ (cpmap cp).map h r₀ (cpmap cp).cpring
      (qs.rotate (qs.length - n % qs.length)) := by
  set r := (cpmap cp).cpring with hr
  have hlen : qs.length = r.length := by
    have := length_eq_of_rqsFit G₀ (cpmap cp).map h hq.fit
    simpa using this
  set k := r.length - n % r.length with hk
  have hk' : qs.length - n % qs.length = k := by rw [hk, hlen]
  have hrot : (r.rotate n).rotate k = r := rotate_rotate_sub_mod _ n
  have hrot' : ((r.map h).rotate n).rotate k = r.map h := by
    have := rotate_rotate_sub_mod (r.map h) n
    rwa [List.length_map] at this
  have hmaprot : (r.rotate n).map h = (r.map h).rotate n := List.map_rotate h r n
  have hperm : (rqsWalk G₀ (qs.rotate k) (r.map h)).Perm
      (rqsWalk G₀ qs ((r.map h).rotate n)) := by
    have hlen2 : qs.length = (((r.map h)).rotate n).length := by simp [hlen]
    have := rqsWalk_rotate G₀ hlen2 k
    rwa [hrot'] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hk']
    have := rqsFit_rotate G₀ (cpmap cp).map h k hq.fit
    rwa [hrot] at this
  · intro u hu hnr hnb
    refine hq.ringArity u hu hnr ?_
    rw [hmaprot]
    exact fun hc => hnb (Hypermap.fband_rotate.mp hc)
  · have hUq := hq.simple
    rw [hmaprot] at hUq
    rw [hk']
    exact hUq.perm (List.Perm.append_right _ hperm.symm)
  · intro u
    have hEq := hq.cover u
    rw [hmaprot] at hEq
    rw [hk', Hypermap.fband_append, fband_perm hperm, ← Hypermap.fband_append, hEq,
      Hypermap.fband_rotate]

/-! #### The two darts of the initial map -/

/-- The edge map of the initial map swaps its two darts. -/
private theorem edge_cpmap0 (b : Bool) : (cpmap []).map.edge b = !b := rfl

/-- Every face of the initial map has a single dart. -/
private theorem arity_cpmap0 (b : Bool) : (cpmap []).map.arity b = 1 := by
  have hmem : ∀ y, y ∈ ([b] : List Bool) ↔ (cpmap []).map.CFace b y := by
    intro y
    rw [cface_cpmap0 b y]
    simp only [List.mem_singleton]
    exact eq_comm
  exact arity_eq_length (List.nodup_singleton _) hmem

/-- Unfolding the compiler at the end of the program. -/
theorem cfquizRec_nil (rq₁ rq₂ : RingQuestion) (qs : List RingQuestion) :
    cfquizRec [] (rq₁ :: rq₂ :: qs) =
      if rq₁.isKernel && rq₂.isKernel then
        if (largeQArity (rq₁.outerArity - 1)).toNat = rq₁.outerArity + 1 ∧
            ¬ BadSmallArity (smallQArity (rq₂.outerArity - 1)) then
          ⟨.askR (largeQArity (rq₁.outerArity - 1)) rq₂.question,
           .askR (smallQArity (rq₂.outerArity - 1)) rq₁.question⟩
        else noquiz
      else noquiz := rfl

/-- Unfolding a walk that starts with a right move. -/
private theorem walkq_askR {D : Type*} (G : Hypermap D) (x : D) (qa : QArity) (q : Question) :
    G.walkq x (.askR qa q) = x :: G.walkq (G.qstepR x) q := rfl

/-- Unfolding the arities recorded by a question that starts with a right
move. -/
private theorem flat_askR (qa : QArity) (q : Question) :
    (Question.askR qa q).flat = qa.toNat :: q.flat := rfl


/-- The walk of a ring question whose dart is in the kernel. -/
private theorem rqsWalk_cons_kernel {D₀ : Type*} (G₀ : Hypermap D₀) (rq : RingQuestion)
    (qs : List RingQuestion) (u : D₀) (p : List D₀) (hk : rq.isKernel = true) :
    rqsWalk G₀ (rq :: qs) (u :: p) =
      u :: (G₀.walkq (G₀.node u) rq.question ++ rqsWalk G₀ qs p) := by
  rw [rqsWalk_cons, hk]
  rfl

/-- **The end of the compilation**: when the program is exhausted the two
remaining ring questions form a valid quiz for the ring of the full map. -/
theorem cfquizRec_nil_valid {D₀ : Type*} (G₀ : Hypermap D₀) (r₀ : List D₀)
    (h : (cpmap []).Dart → D₀)
    (hE : ∀ x, h ((cpmap []).map.edge x) = G₀.edge (h x))
    (qs : List RingQuestion)
    (hq : RqsProper G₀ (cpmap []).map h r₀ (cpmap []).cpring qs)
    (hR : (cfquizRec [] qs).IsQuizR) :
    (∀ u ∈ r₀, G₀.GoodRingArity u) ∧ ∃ x₀, G₀.ValidQuiz r₀ x₀ (cfquizRec [] qs) := by
  obtain ⟨hfit, hnFr, hUq, hEq⟩ := hq
  have hring : (cpmap ([] : CProg)).cpring = [false, true] := PointedMap.cpring_cpmap0
  rw [hring] at hfit hnFr hUq hEq
  have hnFr' : ∀ u ∈ r₀, u ∉ Set.range h → ¬ G₀.Fband [h false, h true] u →
      G₀.GoodRingArity u := hnFr
  have hUq' : G₀.Simple (rqsWalk G₀ qs [h false, h true] ++ r₀) := hUq
  have hEq' : ∀ u, G₀.Fband (rqsWalk G₀ qs [h false, h true] ++ r₀) u ↔
      (u ∉ Set.range h ∨ G₀.Fband [h false, h true] u) := hEq
  clear hnFr hUq hEq
  have hlen : qs.length = 2 := by
    have hl := length_eq_of_rqsFit G₀ (cpmap []).map h hfit
    exact hl
  obtain ⟨rq₁, rq₂, rfl⟩ : ∃ a b, qs = [a, b] := by
    match qs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hfit' : (G₀.arity (h false) = rq₁.outerArity + (cpmap []).map.arity false ∧
      G₀.Fitq (G₀.node (h false)) rq₁.question ∧
      (G₀.arity (h true) = rq₂.outerArity + (cpmap []).map.arity true ∧
        G₀.Fitq (G₀.node (h true)) rq₂.question ∧ True)) := hfit
  obtain ⟨ha1, hq1, ha2, hq2, -⟩ := hfit'
  rw [arity_cpmap0] at ha1 ha2
  rw [cfquizRec_nil] at hR ⊢
  split_ifs at hR ⊢ with hk hcond
  · obtain ⟨hk1, hk2⟩ := Bool.and_eq_true _ _ |>.mp hk
    have hqa1 : (largeQArity (rq₁.outerArity - 1)).toNat = rq₁.outerArity + 1 := hcond.1
    have hqa2 : (smallQArity (rq₂.outerArity - 1)).toNat = rq₂.outerArity + 1 := by
      have h2 : (smallQArity (rq₂.outerArity - 1)).toNat = (rq₂.outerArity - 1) + 2 := by
        by_contra hc
        exact hcond.2 ((badSmallArity_smallQArity _).mpr hc)
      rcases Nat.eq_zero_or_pos rq₂.outerArity with h0 | hpos
      · rw [h0] at h2
        exact absurd h2 (by decide)
      · omega
    have he1 : G₀.edge (h false) = h true := by
      have h1 := hE false
      rw [edge_cpmap0] at h1
      simpa using h1.symm
    have he0 : G₀.edge (h true) = h false := by
      have h1 := hE true
      rw [edge_cpmap0] at h1
      simpa using h1.symm
    have hwalk : G₀.walkqz (h false)
        ⟨.askR (largeQArity (rq₁.outerArity - 1)) rq₂.question,
         .askR (smallQArity (rq₂.outerArity - 1)) rq₁.question⟩
        = (h false :: G₀.walkq (G₀.node (h true)) rq₂.question)
          ++ (h true :: G₀.walkq (G₀.node (h false)) rq₁.question) := by
      simp only [Hypermap.walkqz, walkq_askR, Hypermap.qstepR, he1, he0]
    have hW : rqsWalk G₀ [rq₁, rq₂] [h false, h true]
        = h false :: (G₀.walkq (G₀.node (h false)) rq₁.question
            ++ (h true :: G₀.walkq (G₀.node (h true)) rq₂.question)) := by
      rw [rqsWalk_cons_kernel G₀ _ _ _ _ hk1, rqsWalk_cons_kernel G₀ _ _ _ _ hk2,
        rqsWalk_nil_left, List.append_nil]
    have hperm : (rqsWalk G₀ [rq₁, rq₂] [h false, h true]).Perm
        (G₀.walkqz (h false)
          ⟨.askR (largeQArity (rq₁.outerArity - 1)) rq₂.question,
           .askR (smallQArity (rq₂.outerArity - 1)) rq₁.question⟩) := by
      rw [hwalk, hW, List.cons_append]
      refine List.Perm.cons _ ?_
      refine List.perm_middle.trans (List.Perm.trans ?_ List.perm_middle.symm)
      exact List.Perm.cons _ List.perm_append_comm
    have hfitqz : G₀.Fitqz (h false)
        ⟨.askR (largeQArity (rq₁.outerArity - 1)) rq₂.question,
         .askR (smallQArity (rq₂.outerArity - 1)) rq₁.question⟩ := by
      have hq1' : rq₁.question.flat
          = (G₀.walkq (G₀.node (h false)) rq₁.question).map G₀.arity := hq1
      have hq2' : rq₂.question.flat
          = (G₀.walkq (G₀.node (h true)) rq₂.question).map G₀.arity := hq2
      change Quiz.flat _ = _
      rw [Quiz.flat, hwalk, flat_askR, flat_askR, List.map_append, List.map_cons,
        List.map_cons, ← hq1', ← hq2', ha1, ha2, hqa1, hqa2]
    obtain ⟨hs1, -, hdisj⟩ := Hypermap.simple_append.mp hUq'
    have hrange : ∀ x : Bool, G₀.Fband [h false, h true] (h x) := by
      intro x
      cases x
      · exact Hypermap.fband_cons.mpr (Or.inl (Equiv.Perm.SameCycle.refl _ _))
      · exact Hypermap.fband_cons.mpr
          (Or.inr (Hypermap.fband_cons.mpr (Or.inl (Equiv.Perm.SameCycle.refl _ _))))
    refine ⟨fun u hu => ?_, ?_⟩
    · have hnb : ¬ G₀.Fband [h false, h true] u := by
        intro hb
        rcases Hypermap.fband_cons.mp hb with hc | hc
        · exact hdisj (h false) (by rw [hW]; exact List.mem_cons_self) ⟨u, hu, hc.symm⟩
        · rcases Hypermap.fband_cons.mp hc with hc2 | hc2
          · refine hdisj (h true) ?_ ⟨u, hu, hc2.symm⟩
            rw [hW]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
          · exact absurd hc2 (by simp)
      have hnr : u ∉ Set.range h := by
        rintro ⟨x, rfl⟩
        exact hnb (hrange x)
      exact hnFr' u hu hnr hnb
    · refine ⟨h false, ⟨trivial, trivial⟩, hfitqz, hs1.perm hperm, fun y => ?_⟩
      constructor
      · intro hy hb
        rw [← fband_perm hperm] at hy
        obtain ⟨v, hv, hyv⟩ := hy
        exact hdisj v hv ((Hypermap.Fband.congr hyv).mp hb)
      · intro hb
        rw [← fband_perm hperm]
        have h2 : G₀.Fband (rqsWalk G₀ [rq₁, rq₂] [h false, h true] ++ r₀) y := by
          refine (hEq' y).mpr ?_
          by_cases hr : y ∈ Set.range h
          · obtain ⟨x, rfl⟩ := hr
            exact Or.inr (hrange x)
          · exact Or.inl hr
        rcases Hypermap.fband_append.mp h2 with hc | hc
        · exact hc
        · exact absurd hc hb
  · exact absurd hR not_isQuizR_noquiz
  · exact absurd hR not_isQuizR_noquiz


/-! #### Geometry of a `Y` step

The lemmas below locate the four darts a `Y` step adds, and compute the two
node steps that link the new ring question to the two it replaces. -/

/-- The ring of a `Y` step, with its head computed. -/
private theorem cpring_ecpY_eq (M : PointedMap) :
    M.ecpY.cpring = (.icp .Xe : M.ecpY.Dart) :: .X :: M.cpring.tail.map M.icpY := by
  rw [PointedMap.cpring_ecpY', PointedMap.node_ecpY]
  rfl

/-- The perimeter of a pointed map starts at the node of its reference dart. -/
private theorem head_cpring_pointed (M : PointedMap) :
    M.cpring = M.map.node M.point :: M.cpring.tail := Hypermap.head_cpring

/-- The perimeter of a nontrivial pointed map starts `node x₀ :: x₀ :: …`. -/
private theorem head_proper_cpring_pointed (M : PointedMap) (hp : M.Proper) :
    M.cpring = M.map.node M.point :: M.point :: M.cpring.drop 2 :=
  Hypermap.head_proper_cpring hp

/-- The perimeter of a pointed map has no repetitions. -/
private theorem nodup_cpring_pointed (M : PointedMap) : M.cpring.Nodup :=
  Hypermap.nodup_cpring

/-- **Every dart of a `Y` step** is either an old dart, or lies on the face of
the new dart, of `x₀`, or of `node x₀`. -/
private theorem ecpY_dart_cases (M : PointedMap) (hp : M.Proper)
    (x : EcpDart (EcpDart M.Dart)) :
    (∃ y : M.Dart, x = M.icpY y) ∨ M.ecpY.map.CFace (.X : M.ecpY.Dart) x
      ∨ M.ecpY.map.CFace x (M.icpY M.point)
      ∨ M.ecpY.map.CFace x (M.icpY (M.map.node M.point)) := by
  cases x with
  | X => exact Or.inr (Or.inl (Equiv.Perm.SameCycle.refl _ _))
  | Xe => exact Or.inr (Or.inr (Or.inl (Hypermap.cface_Xe_ecpY M.map M.point hp)))
  | icp w =>
    cases w with
    | X => exact Or.inr (Or.inl ((PointedMap.cface_ecpY M _).mpr (Or.inr rfl)))
    | Xe => exact Or.inr (Or.inr (Or.inr (Hypermap.cface_icpXe_ecpY M.map M.point)))
    | icp y => exact Or.inl ⟨y, rfl⟩

/-- The node of the image of `node x₀` after a `Y` step. -/
private theorem node_icpY_node (M : PointedMap) :
    M.ecpY.map.node (M.icpY (M.map.node M.point)) = (.icp .X : M.ecpY.Dart) := by
  have hU2 : (Hypermap.ecpUMap M.map M.point).node (.icp (M.map.node M.point)) = .X :=
    ite_eq_left rfl
  have h2 : (Hypermap.ecpUMap M.map M.point).node
      ((Hypermap.ecpUMap M.map M.point).node (.icp (M.map.node M.point))) ≠ .X := by
    rw [hU2]
    intro hc
    exact absurd (show (EcpDart.Xe : EcpDart M.Dart) = .X from hc) (by simp)
  have hne : (EcpDart.icp (M.map.node M.point) : EcpDart M.Dart) ≠ .X := by simp
  rw [show M.ecpY.map.node (M.icpY (M.map.node M.point))
      = (Hypermap.ecpNMap (Hypermap.ecpUMap M.map M.point) .X).node
          (.icp (.icp (M.map.node M.point))) from rfl,
    Hypermap.node_ecpY_of M.map M.point (.icp (M.map.node M.point)) hne h2, hU2]
  rfl

/-- The node of the dart just after the image of `node x₀` in a `Y` step. -/
private theorem node_icp_X_ecpY (M : PointedMap) :
    M.ecpY.map.node (.icp .X : M.ecpY.Dart) = (.Xe : M.ecpY.Dart) := rfl

/-- The image of an old dart is never one of the two darts a `Y` step adds on
top of the `U` step. -/
private theorem icpY_ne_icp_Xe (M : PointedMap) (y : M.Dart) :
    (M.icpY y : EcpDart (EcpDart M.Dart)) ≠ .icp .Xe := by
  intro hc
  injection hc with h1
  injection h1

/-- The image of an old dart is never the new dart of a `Y` step. -/
private theorem icpY_ne_X (M : PointedMap) (y : M.Dart) :
    (M.icpY y : EcpDart (EcpDart M.Dart)) ≠ .X := by
  intro hc
  injection hc

/-- The image of an old dart is never the dart after the new one. -/
private theorem icpY_ne_icp_X (M : PointedMap) (y : M.Dart) :
    (M.icpY y : EcpDart (EcpDart M.Dart)) ≠ .icp .X := by
  intro hc
  injection hc with h1
  injection h1

/-- One node step back from the image of `node x₀` reaches the node of the new
dart. -/
private theorem edge_node_icpY_node (M : PointedMap) :
    M.ecpY.map.edge (M.ecpY.map.node (M.icpY (M.map.node M.point)))
      = M.ecpY.map.node .X := by
  rw [node_icpY_node, PointedMap.node_ecpY]
  rfl

/-- Two node steps back from the image of `node x₀` reaches the new dart. -/
private theorem edge_node_node_icpY_node (M : PointedMap) :
    M.ecpY.map.edge (M.ecpY.map.node (M.ecpY.map.node (M.icpY (M.map.node M.point))))
      = (.X : M.ecpY.Dart) := by
  rw [node_icpY_node, node_icp_X_ecpY]
  rfl

/-- The image of `node x₀` is not on the ring of a `Y` step. -/
private theorem not_mem_cpring_icpY_node (M : PointedMap) :
    M.icpY (M.map.node M.point) ∉ M.ecpY.cpring := by
  rw [cpring_ecpY_eq]
  intro hc
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (M.icpY (M.map.node M.point) : EcpDart (EcpDart M.Dart))
      = .icp .Xe from h1) (icpY_ne_icp_Xe M _)
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (M.icpY (M.map.node M.point) : EcpDart (EcpDart M.Dart))
      = .X from h1) (icpY_ne_X M _)
  obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hc
  have hy' : y = M.map.node M.point :=
    PointedMap.icpY_injective M
      (show (M.icpY y : EcpDart (EcpDart M.Dart)) = M.icpY (M.map.node M.point) from hyeq)
  subst hy'
  have hnd : (M.map.node M.point :: M.cpring.tail).Nodup := by
    rw [← head_cpring_pointed M]
    exact nodup_cpring_pointed M
  exact (List.nodup_cons.mp hnd).1 hy

/-- The dart just after the image of `node x₀` is not on the ring of a `Y`
step. -/
private theorem not_mem_cpring_icp_X_ecpY (M : PointedMap) :
    (.icp .X : M.ecpY.Dart) ∉ M.ecpY.cpring := by
  rw [cpring_ecpY_eq]
  intro hc
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (EcpDart.icp EcpDart.X : EcpDart (EcpDart M.Dart)) = .icp .Xe from h1)
      (by simp)
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (EcpDart.icp EcpDart.X : EcpDart (EcpDart M.Dart)) = .X from h1)
      (by simp)
  obtain ⟨y, -, hy⟩ := List.mem_map.mp hc
  exact absurd (show (M.icpY y : EcpDart (EcpDart M.Dart)) = .icp .X from hy)
    (icpY_ne_icp_X M y)


/-- Transferring the fit along an injection that preserves arities. -/
private theorem rqsFit_map_iff {D₀ D D' : Type*} (G₀ : Hypermap D₀) (G : Hypermap D)
    (G' : Hypermap D') (h : D' → D₀) (f : D → D') :
    ∀ (qs : List RingQuestion) (p : List D), (∀ x ∈ p, G'.arity (f x) = G.arity x) →
      (rqsFit G₀ G' h qs (p.map f) ↔ rqsFit G₀ G (fun x => h (f x)) qs p) := by
  intro qs
  induction qs with
  | nil =>
    intro p _
    cases p with
    | nil => exact Iff.rfl
    | cons x p => exact Iff.rfl
  | cons rq qs ih =>
    intro p hp
    cases p with
    | nil => exact Iff.rfl
    | cons x p =>
      rw [List.map_cons, rqsFit_cons, rqsFit_cons,
        ih p (fun y hy => hp y (List.mem_cons_of_mem _ hy)),
        hp x List.mem_cons_self]

/-- The question a `Y` step attaches to the first ring face when the second
ring dart is in the kernel: the two old questions are hung below a new arity
test. -/
def mergeQY (qa : QArity) (q₁ q₂ : Question) : Question :=
  match q₁, q₂ with
  | .ask0, .ask0 => .ask1 qa
  | .ask0, q₂ => .askL qa q₂
  | q₁, .ask0 => .askR qa q₁
  | q₁, q₂ => .askLR qa q₂ q₁

/-- The merged question records the same arities as the general one. -/
private theorem flat_mergeQY (qa : QArity) (q₁ q₂ : Question) :
    (mergeQY qa q₁ q₂).flat = (Question.askLR qa q₂ q₁).flat := by
  cases q₁ <;> cases q₂ <;> simp [mergeQY, Question.flat]

/-- The merged question visits the same darts as the general one. -/
private theorem walkq_mergeQY {D : Type*} (G : Hypermap D) (x : D) (qa : QArity)
    (q₁ q₂ : Question) :
    G.walkq x (mergeQY qa q₁ q₂) = G.walkq x (.askLR qa q₂ q₁) := by
  cases q₁ <;> cases q₂ <;> simp [mergeQY, Hypermap.walkq]

/-- A `Y` step at a kernel dart merges the two questions. -/
theorem cfquizY_of_kernel (rq₁ rq₂ : RingQuestion) (k : Question → List RingQuestion)
    (hk : rq₂.isKernel = true) (hb : ¬ BadSmallArity (smallQArity rq₂.outerArity)) :
    cfquizY rq₁ rq₂ k
      = k (mergeQY (smallQArity rq₂.outerArity) rq₁.question rq₂.question) := by
  rw [cfquizY, ite_eq_left hk, ite_eq_right hb]
  congr 1

/-- A `Y` step at a ring dart passes the two questions on unchanged, when it
can. -/
theorem cfquizY_of_not_kernel (rq₁ rq₂ : RingQuestion) (k : Question → List RingQuestion)
    (hk : rq₂.isKernel = false) (hb : ¬ BadRingArity rq₂.outerArity) :
    cfquizY rq₁ rq₂ k
      = (match rq₁.question, rq₂.question with
         | .ask0, .ask0 => k .ask0
         | .askR qa₁ q₁r, .ask0 => k (.askRR qa₁ q₁r)
         | .ask0, .askL qa₁ q₁l => k (.askLL qa₁ q₁l)
         | _, _ => []) := by
  have hk' : ¬ (rq₂.isKernel = true) := by simp [hk]
  rw [cfquizY, ite_eq_right hk', ite_eq_right hb]

/-- A successful `Y` step at a kernel dart passes the small arity check. -/
theorem not_badSmallArity_of_cfquizY {rq₁ rq₂ : RingQuestion}
    {k : Question → List RingQuestion} (hk : rq₂.isKernel = true)
    (hne : cfquizY rq₁ rq₂ k ≠ []) : ¬ BadSmallArity (smallQArity rq₂.outerArity) := by
  intro hb
  refine hne ?_
  rw [cfquizY, ite_eq_left hk, ite_eq_left hb]

/-- A successful `Y` step at a ring dart passes the ring arity check. -/
theorem not_badRingArity_of_cfquizY {rq₁ rq₂ : RingQuestion}
    {k : Question → List RingQuestion} (hk : rq₂.isKernel = false)
    (hne : cfquizY rq₁ rq₂ k ≠ []) : ¬ BadRingArity rq₂.outerArity := by
  intro hb
  refine hne ?_
  have hk' : ¬ (rq₂.isKernel = true) := by simp [hk]
  rw [cfquizY, ite_eq_right hk', ite_eq_left hb]


/-- The band of a one-dart list. -/
private theorem fband_singleton {D : Type*} {G : Hypermap D} (a x : D) :
    G.Fband [a] x ↔ G.CFace x a := by simp

/-- Unfolding an empty walk. -/
private theorem walkq_ask0 {D : Type*} (G : Hypermap D) (x : D) :
    G.walkq x .ask0 = [] := rfl

/-- Unfolding a one-dart walk. -/
private theorem walkq_ask1 {D : Type*} (G : Hypermap D) (x : D) (qa : QArity) :
    G.walkq x (.ask1 qa) = [x] := rfl

/-- Unfolding a walk that starts with a left move. -/
private theorem walkq_askL {D : Type*} (G : Hypermap D) (x : D) (qa : QArity) (q : Question) :
    G.walkq x (.askL qa q) = x :: G.walkq (G.qstepL x) q := rfl

/-- Unfolding a walk that branches both ways. -/
private theorem walkq_askLR {D : Type*} (G : Hypermap D) (x : D) (qa : QArity)
    (ql qr : Question) :
    G.walkq x (.askLR qa ql qr)
      = x :: (G.walkq (G.qstepL x) ql ++ G.walkq (G.qstepR x) qr) := rfl

/-- Unfolding a walk that starts with a doubled left move. -/
private theorem walkq_askLL {D : Type*} (G : Hypermap D) (x : D) (qa : QArity) (q : Question) :
    G.walkq x (.askLL qa q)
      = G.edge (G.node (G.qstepL x)) :: G.walkq (G.qstepL (G.qstepL x)) q := rfl

/-- Unfolding a walk that starts with a doubled right move. -/
private theorem walkq_askRR {D : Type*} (G : Hypermap D) (x : D) (qa : QArity) (q : Question) :
    G.walkq x (.askRR qa q) = G.qstepR x :: G.walkq (G.qstepR (G.qstepR x)) q := rfl

/-- The arities recorded by the empty question. -/
private theorem flat_ask0 : (Question.ask0).flat = [] := rfl

/-- The arities recorded by a one-face question. -/
private theorem flat_ask1 (qa : QArity) : (Question.ask1 qa).flat = [qa.toNat] := rfl

/-- The arities recorded by a left question. -/
private theorem flat_askL (qa : QArity) (q : Question) :
    (Question.askL qa q).flat = qa.toNat :: q.flat := rfl

/-- The arities recorded by a branching question. -/
private theorem flat_askLR (qa : QArity) (ql qr : Question) :
    (Question.askLR qa ql qr).flat = qa.toNat :: (ql.flat ++ qr.flat) := rfl

/-- The arities recorded by a doubled left question. -/
private theorem flat_askLL (qa : QArity) (q : Question) :
    (Question.askLL qa q).flat = qa.toNat :: q.flat := rfl

/-- The arities recorded by a doubled right question. -/
private theorem flat_askRR (qa : QArity) (q : Question) :
    (Question.askRR qa q).flat = qa.toNat :: q.flat := rfl

/-- One edge step back from a node lands on the same face. -/
private theorem cface_edge_node {D : Type*} (G : Hypermap D) (z : D) :
    G.CFace (G.edge (G.node z)) z := by
  have hz : G.face (G.edge (G.node z)) = z := by
    rw [Hypermap.face_edge, Hypermap.inv_node_node]
  have h1 : G.CFace (G.edge (G.node z)) (G.face (G.edge (G.node z))) := G.cface_face _
  rwa [hz] at h1

/-- One edge step back from a node does not change the arity. -/
private theorem arity_edge_node' {D : Type*} [Finite D] (G : Hypermap D) (z : D) :
    G.arity (G.edge (G.node z)) = G.arity z :=
  Hypermap.arity_cface _ (cface_edge_node G z)


/-- The three shapes a `Y` step at a ring dart can handle. -/
theorem cfquizY_not_kernel_cases {rq₁ rq₂ : RingQuestion} {k : Question → List RingQuestion}
    (hk : rq₂.isKernel = false) (hne : cfquizY rq₁ rq₂ k ≠ []) :
    (rq₁.question = .ask0 ∧ rq₂.question = .ask0 ∧ cfquizY rq₁ rq₂ k = k .ask0)
      ∨ (∃ qa q, rq₁.question = .askR qa q ∧ rq₂.question = .ask0
          ∧ cfquizY rq₁ rq₂ k = k (.askRR qa q))
      ∨ (∃ qa q, rq₁.question = .ask0 ∧ rq₂.question = .askL qa q
          ∧ cfquizY rq₁ rq₂ k = k (.askLL qa q)) := by
  have hb := not_badRingArity_of_cfquizY hk hne
  have heq := cfquizY_of_not_kernel rq₁ rq₂ k hk hb
  cases hq1 : rq₁.question
  case ask0 =>
    cases hq2 : rq₂.question
    case ask0 => exact Or.inl ⟨rfl, rfl, by rw [heq, hq1, hq2]⟩
    case askL qa q => exact Or.inr (Or.inr ⟨qa, q, rfl, rfl, by rw [heq, hq1, hq2]⟩)
    all_goals exact absurd (by rw [heq, hq1, hq2]) hne
  case askR qa q =>
    cases hq2 : rq₂.question
    case ask0 => exact Or.inr (Or.inl ⟨qa, q, rfl, rfl, by rw [heq, hq1, hq2]⟩)
    all_goals exact absurd (by rw [heq, hq1, hq2]) hne
  all_goals
    cases hq2 : rq₂.question <;> exact absurd (by rw [heq, hq1, hq2]) hne

/-- **A `Y` step preserves the invariant**: the new ring question merges the two
questions of the ring darts the step removes. -/
theorem rqsProper_Y {D₀ : Type*} [Finite D₀] (G₀ : Hypermap D₀) (r₀ : List D₀)
    (M : PointedMap)
    (hp : M.Proper) (hUr : M.map.Simple M.cpring) (h : M.ecpY.Dart → D₀)
    (hE : ∀ x, h (M.ecpY.map.edge x) = G₀.edge (h x))
    (hN : ∀ x, x ∉ M.ecpY.cpring → h (M.ecpY.map.node x) = G₀.node (h x))
    (hF : ∀ x y, G₀.CFace (h x) (h y) ↔ M.ecpY.map.CFace x y)
    (rq₁ rq₂ rq₃ : RingQuestion) (qs : List RingQuestion)
    (hq : RqsProper G₀ M.ecpY.map h r₀ M.ecpY.cpring (rq₁ :: rq₂ :: rq₃ :: qs))
    (hne : cfquizY rq₁ rq₂ (rqsY rq₁ rq₃ qs) ≠ []) :
    RqsProper G₀ M.map (fun x => h (M.icpY x)) r₀ M.cpring
      (cfquizY rq₁ rq₂ (rqsY rq₁ rq₃ qs)) := by
  have hr : M.cpring = M.map.node M.point :: M.point :: M.cpring.drop 2 :=
    head_proper_cpring_pointed M hp
  have htail : M.cpring.tail = M.point :: M.cpring.drop 2 := by
    conv_lhs => rw [hr]
    rfl
  have hringY : M.ecpY.cpring
      = M.ecpY.map.node .X :: (.X : M.ecpY.Dart) :: M.icpY M.point
        :: (M.cpring.drop 2).map M.icpY := by
    rw [PointedMap.cpring_ecpY', htail, List.map_cons]
  have hUr2 : M.map.Simple (M.map.node M.point :: M.point :: M.cpring.drop 2) := hr ▸ hUr
  have hnp : ¬ M.map.CFace (M.map.node M.point) M.point := fun hc =>
    hUr2.not_fband ⟨M.point, List.mem_cons_self, hc⟩
  have hpn : ¬ M.map.CFace M.point (M.map.node M.point) := fun hc => hnp hc.symm
  have hr1n : ∀ x ∈ M.cpring.drop 2, ¬ M.map.CFace x (M.map.node M.point) := fun x hx hc =>
    hUr2.not_fband ⟨x, List.mem_cons_of_mem _ hx, hc.symm⟩
  have hr1p : ∀ x ∈ M.cpring.drop 2, ¬ M.map.CFace x M.point := fun x hx hc =>
    hUr2.of_cons.not_fband ⟨x, hx, hc.symm⟩
  have hAu0 : M.ecpY.map.arity (.X : M.ecpY.Dart) = 2 := arity_ecpY_X M hp
  have hAv1 : M.ecpY.map.arity (M.icpY (M.map.node M.point))
      = M.map.arity (M.map.node M.point) + 1 :=
    arity_icpY_of_node M hp (Equiv.Perm.SameCycle.refl _ _) hnp
  have hAv2 : M.ecpY.map.arity (M.icpY M.point) = M.map.arity M.point + 1 :=
    arity_icpY_of_point M hp hpn (Equiv.Perm.SameCycle.refl _ _)
  have hAr1 : ∀ x ∈ M.cpring.drop 2, M.ecpY.map.arity (M.icpY x) = M.map.arity x :=
    fun x hx => arity_icpY_of_not M hp (hr1n x hx) (hr1p x hx)
  have hnu0F : M.ecpY.map.CFace (M.ecpY.map.node .X) (M.icpY (M.map.node M.point)) :=
    PointedMap.cface_node_ecpY' M
  have hAnu0 : M.ecpY.map.arity (M.ecpY.map.node (.X : M.ecpY.Dart))
      = M.map.arity (M.map.node M.point) + 1 := by
    rw [Hypermap.arity_cface _ hnu0F, hAv1]
  have hfitY : rqsFit G₀ M.ecpY.map h (rq₁ :: rq₂ :: rq₃ :: qs)
      (M.ecpY.map.node .X :: (.X : M.ecpY.Dart) :: M.icpY M.point
        :: (M.cpring.drop 2).map M.icpY) := by
    rw [← hringY]
    exact hq.fit
  obtain ⟨Ea1, hqu1, Ea2, hqu2, Ea3, hqu3, hqr1⟩ := hfitY
  have hfit1 : rqsFit G₀ M.map (fun x => h (M.icpY x)) qs (M.cpring.drop 2) :=
    (rqsFit_map_iff G₀ M.map M.ecpY.map h M.icpY qs (M.cpring.drop 2) hAr1).mp hqr1
  have hfaceY : G₀.CFace (h (M.ecpY.map.node .X)) (h (M.icpY (M.map.node M.point))) :=
    (hF _ _).mpr hnu0F
  have hA1 : G₀.arity (h (M.icpY (M.map.node M.point)))
      = (rq₁.outerArity + 1) + M.map.arity (M.map.node M.point) := by
    rw [← Hypermap.arity_cface _ hfaceY, Ea1, hAnu0]
    omega
  have hA3 : G₀.arity (h (M.icpY M.point)) = (rq₃.outerArity + 1) + M.map.arity M.point := by
    rw [Ea3, hAv2]
    omega
  have hA2 : G₀.arity (h (.X : M.ecpY.Dart)) = rq₂.outerArity + 2 := by rw [Ea2, hAu0]
  have hnv1 : G₀.node (h (M.icpY (M.map.node M.point)))
      = h (M.ecpY.map.node (M.icpY (M.map.node M.point))) :=
    (hN _ (not_mem_cpring_icpY_node M)).symm
  have hen : G₀.edge (G₀.node (h (M.icpY (M.map.node M.point))))
      = h (M.ecpY.map.node (.X : M.ecpY.Dart)) := by
    rw [hnv1, ← hE, edge_node_icpY_node]
  have hnn : G₀.node (G₀.node (h (M.icpY (M.map.node M.point))))
      = h (M.ecpY.map.node (.icp .X : M.ecpY.Dart)) := by
    rw [hnv1, node_icpY_node, hN _ (not_mem_cpring_icp_X_ecpY M)]
  have henn : G₀.edge (G₀.node (G₀.node (h (M.icpY (M.map.node M.point)))))
      = h (.X : M.ecpY.Dart) := by
    rw [hnn, ← hE, node_icp_X_ecpY]
    rfl
  have hqR : G₀.qstepR (G₀.node (h (M.icpY (M.map.node M.point))))
      = G₀.node (h (M.ecpY.map.node .X)) := by rw [Hypermap.qstepR, hen]
  have hqL : G₀.qstepL (G₀.node (h (M.icpY (M.map.node M.point))))
      = G₀.node (h (.X : M.ecpY.Dart)) := by rw [Hypermap.qstepL, henn]
  have hfaceu0 : G₀.face (h (.X : M.ecpY.Dart))
      = G₀.node (h (M.icpY (M.map.node M.point))) := by
    rw [← henn, Hypermap.face_edge, Hypermap.inv_node_node]
  have hAnv1 : G₀.arity (G₀.node (h (M.icpY (M.map.node M.point)))) = rq₂.outerArity + 2 := by
    rw [← hfaceu0, Hypermap.arity_face, hA2]
  have hcfu0 : G₀.CFace (h (.X : M.ecpY.Dart))
      (G₀.node (h (M.icpY (M.map.node M.point)))) := by
    rw [← hfaceu0]
    exact G₀.cface_face _
  have hmap1 : M.cpring.map (fun x => h (M.icpY x))
      = h (M.icpY (M.map.node M.point)) :: h (M.icpY M.point)
        :: ((M.cpring.drop 2).map fun x => h (M.icpY x)) := by
    rw [hr]
    rfl
  have hmapY : M.ecpY.cpring.map h
      = h (M.ecpY.map.node .X) :: h (.X : M.ecpY.Dart) :: h (M.icpY M.point)
        :: ((M.cpring.drop 2).map fun x => h (M.icpY x)) := by
    rw [hringY]
    have hcons : List.map h (M.ecpY.map.node .X :: (.X : M.ecpY.Dart) :: M.icpY M.point
        :: (M.cpring.drop 2).map M.icpY)
        = h (M.ecpY.map.node .X) :: h (.X : M.ecpY.Dart) :: h (M.icpY M.point)
          :: (((M.cpring.drop 2).map M.icpY).map h) := rfl
    rw [hcons, List.map_map]
    rfl
  have hP : ∀ u, (u ∉ Set.range h ∨ G₀.Fband (M.ecpY.cpring.map h) u)
      ↔ (u ∉ Set.range (fun x => h (M.icpY x))
          ∨ G₀.Fband (M.cpring.map fun x => h (M.icpY x)) u) := by
    intro u
    rw [hmap1, hmapY]
    constructor
    · rintro (hu | hu)
      · exact Or.inl fun ⟨x, hx⟩ => hu ⟨M.icpY x, hx⟩
      · rcases Hypermap.fband_cons.mp hu with hc | hu
        · exact Or.inr (Hypermap.fband_cons.mpr (Or.inl (hc.trans hfaceY)))
        · rcases Hypermap.fband_cons.mp hu with hc | hu
          · refine Or.inl ?_
            rintro ⟨z, rfl⟩
            exact absurd ((hF _ _).mp hc).symm (PointedMap.not_cface_ecpY_icpY M z)
          · exact Or.inr (Hypermap.fband_cons.mpr (Or.inr hu))
    · rintro (hu | hu)
      · by_cases hx : u ∈ Set.range h
        · obtain ⟨x, rfl⟩ := hx
          refine Or.inr ?_
          rcases ecpY_dart_cases M hp x with ⟨y, rfl⟩ | hc | hc | hc
          · exact absurd ⟨y, rfl⟩ hu
          · exact Hypermap.fband_cons.mpr
              (Or.inr (Hypermap.fband_cons.mpr (Or.inl ((hF _ _).mpr hc).symm)))
          · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr
              (Or.inr (Hypermap.fband_cons.mpr (Or.inl ((hF _ _).mpr hc))))))
          · exact Hypermap.fband_cons.mpr
              (Or.inl (((hF _ _).mpr hc).trans hfaceY.symm))
        · exact Or.inl hx
      · refine Or.inr ?_
        rcases Hypermap.fband_cons.mp hu with hc | hu
        · exact Hypermap.fband_cons.mpr (Or.inl (hc.trans hfaceY.symm))
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inr hu)))
  suffices H : ∀ q₁' : Question,
      G₀.Fitq (G₀.node (h (M.icpY (M.map.node M.point)))) q₁' →
      (∀ u, G₀.Fband (G₀.walkq (G₀.node (h (M.icpY (M.map.node M.point)))) q₁') u ↔
        (G₀.Fband (G₀.walkq (G₀.node (h (M.ecpY.map.node .X))) rq₁.question) u
          ∨ (rq₂.isKernel = true ∧ G₀.CFace u (h (.X : M.ecpY.Dart)))
          ∨ G₀.Fband (G₀.walkq (G₀.node (h (.X : M.ecpY.Dart))) rq₂.question) u)) →
      q₁'.flat.length = rq₁.question.flat.length
        + (if rq₂.isKernel = true then 1 else 0) + rq₂.question.flat.length →
      RqsProper G₀ M.map (fun x => h (M.icpY x)) r₀ M.cpring (rqsY rq₁ rq₃ qs q₁') by
    cases hk2 : rq₂.isKernel
    · rcases cfquizY_not_kernel_cases hk2 hne with ⟨h1, h2, heq⟩ | ⟨qa, q, h1, h2, heq⟩
        | ⟨qa, q, h1, h2, heq⟩
      · rw [heq]
        refine H .ask0 rfl (fun u => ?_) ?_
        · rw [walkq_ask0, h1, h2, walkq_ask0, walkq_ask0]
          simp [hk2]
        · rw [h1, h2, hk2]
          simp [flat_ask0]
      · rw [heq]
        have hw : G₀.walkq (G₀.node (h (M.icpY (M.map.node M.point)))) (.askRR qa q)
            = G₀.walkq (G₀.node (h (M.ecpY.map.node .X))) (.askR qa q) := by
          rw [walkq_askRR, walkq_askR, hqR]
        have hfit : rq₁.question.flat
            = (G₀.walkq (G₀.node (h (M.ecpY.map.node .X))) rq₁.question).map G₀.arity := hqu1
        refine H (.askRR qa q) ?_ (fun u => ?_) ?_
        · change (Question.askRR qa q).flat = _
          rw [hw, flat_askRR, ← flat_askR, ← h1]
          exact hfit
        · rw [hw, h1, h2, walkq_ask0]
          simp [hk2]
        · rw [h1, h2, hk2]
          simp [flat_askRR, flat_askR, flat_ask0]
      · rw [heq]
        have hw : G₀.walkq (G₀.node (h (M.icpY (M.map.node M.point)))) (.askLL qa q)
            = G₀.edge (G₀.node (G₀.node (h (.X : M.ecpY.Dart))))
              :: G₀.walkq (G₀.qstepL (G₀.node (h (.X : M.ecpY.Dart)))) q := by
          rw [walkq_askLL, hqL]
        have hw2 : G₀.walkq (G₀.node (h (.X : M.ecpY.Dart))) (.askL qa q)
            = G₀.node (h (.X : M.ecpY.Dart))
              :: G₀.walkq (G₀.qstepL (G₀.node (h (.X : M.ecpY.Dart)))) q := walkq_askL _ _ _ _
        have hfit : rq₂.question.flat
            = (G₀.walkq (G₀.node (h (.X : M.ecpY.Dart))) rq₂.question).map G₀.arity := hqu2
        refine H (.askLL qa q) ?_ (fun u => ?_) ?_
        · change (Question.askLL qa q).flat = _
          rw [hw, flat_askLL, List.map_cons, arity_edge_node']
          rw [h2] at hfit
          rw [hw2, List.map_cons, flat_askL] at hfit
          exact hfit
        · rw [hw, h1, h2, hw2, walkq_ask0]
          simp only [Hypermap.fband_cons, Hypermap.fband_nil, hk2, false_and, false_or,
            Bool.false_eq_true]
          constructor
          · rintro (hc | hc)
            · exact Or.inl (hc.trans (cface_edge_node G₀ _))
            · exact Or.inr hc
          · rintro (hc | hc)
            · exact Or.inl (hc.trans (cface_edge_node G₀ _).symm)
            · exact Or.inr hc
        · rw [h1, h2, hk2]
          simp [flat_askLL, flat_askL, flat_ask0]
    · have hb := not_badSmallArity_of_cfquizY hk2 hne
      have hqa2 : (smallQArity rq₂.outerArity).toNat = rq₂.outerArity + 2 := by
        by_contra hc
        exact hb ((badSmallArity_smallQArity _).mpr hc)
      rw [cfquizY_of_kernel rq₁ rq₂ _ hk2 hb]
      have hfitu1 : rq₁.question.flat
          = (G₀.walkq (G₀.node (h (M.ecpY.map.node .X))) rq₁.question).map G₀.arity := hqu1
      have hfitu2 : rq₂.question.flat
          = (G₀.walkq (G₀.node (h (.X : M.ecpY.Dart))) rq₂.question).map G₀.arity := hqu2
      have hw : G₀.walkq (G₀.node (h (M.icpY (M.map.node M.point))))
            (mergeQY (smallQArity rq₂.outerArity) rq₁.question rq₂.question)
          = G₀.node (h (M.icpY (M.map.node M.point)))
            :: (G₀.walkq (G₀.node (h (.X : M.ecpY.Dart))) rq₂.question
              ++ G₀.walkq (G₀.node (h (M.ecpY.map.node .X))) rq₁.question) := by
        rw [walkq_mergeQY, walkq_askLR, hqL, hqR]
      refine H (mergeQY (smallQArity rq₂.outerArity) rq₁.question rq₂.question) ?_
        (fun u => ?_) ?_
      · change (mergeQY _ _ _).flat = _
        rw [hw, flat_mergeQY, flat_askLR, List.map_cons, List.map_append, hAnv1, hqa2,
          ← hfitu1, ← hfitu2]
      · rw [hw]
        simp only [Hypermap.fband_cons, Hypermap.fband_append, hk2, true_and]
        constructor
        · rintro (hc | hc | hc)
          · exact Or.inr (Or.inl (hc.trans hcfu0.symm))
          · exact Or.inr (Or.inr hc)
          · exact Or.inl hc
        · rintro (hc | hc | hc)
          · exact Or.inr (Or.inr hc)
          · exact Or.inl (hc.trans hcfu0)
          · exact Or.inr (Or.inl hc)
      · rw [flat_mergeQY, flat_askLR, hk2]
        simp only [List.length_cons, List.length_append, ite_true]
        omega
  intro q₁' hq1' hband hflen
  have hWold : rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpY.cpring.map h)
      = (if rq₁.isKernel = true then [h (M.ecpY.map.node .X)] else [])
        ++ (G₀.walkq (G₀.node (h (M.ecpY.map.node .X))) rq₁.question
          ++ ((if rq₂.isKernel = true then [h (.X : M.ecpY.Dart)] else [])
            ++ (G₀.walkq (G₀.node (h (.X : M.ecpY.Dart))) rq₂.question
              ++ rqsWalk G₀ (rq₃ :: qs)
                (h (M.icpY M.point) :: ((M.cpring.drop 2).map fun x => h (M.icpY x)))))) := by
    rw [hmapY, rqsWalk_cons, rqsWalk_cons]
  have hWnew : rqsWalk G₀ (rqsY rq₁ rq₃ qs q₁') (M.cpring.map fun x => h (M.icpY x))
      = (if rq₁.isKernel = true then [h (M.icpY (M.map.node M.point))] else [])
        ++ (G₀.walkq (G₀.node (h (M.icpY (M.map.node M.point)))) q₁'
          ++ rqsWalk G₀ (rq₃ :: qs)
            (h (M.icpY M.point) :: ((M.cpring.drop 2).map fun x => h (M.icpY x)))) := by
    rw [hmap1, rqsWalk_cons]
    rfl
  have hK1 : ∀ u, G₀.Fband
        (if rq₁.isKernel = true then [h (M.icpY (M.map.node M.point))] else []) u
      ↔ G₀.Fband (if rq₁.isKernel = true then [h (M.ecpY.map.node .X)] else []) u := by
    intro u
    split_ifs with hk1
    · rw [fband_singleton, fband_singleton]
      exact ⟨fun hc => hc.trans hfaceY.symm, fun hc => hc.trans hfaceY⟩
    · exact Iff.rfl
  have hbandW : ∀ u, G₀.Fband
        (rqsWalk G₀ (rqsY rq₁ rq₃ qs q₁') (M.cpring.map fun x => h (M.icpY x))) u
      ↔ G₀.Fband (rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpY.cpring.map h)) u := by
    intro u
    rw [hWold, hWnew]
    simp only [Hypermap.fband_append, hK1 u, hband u]
    have hk2band : G₀.Fband (if rq₂.isKernel = true then [h (.X : M.ecpY.Dart)] else []) u
        ↔ (rq₂.isKernel = true ∧ G₀.CFace u (h (.X : M.ecpY.Dart))) := by
      split_ifs with hk2
      · rw [fband_singleton]
        exact ⟨fun hc => ⟨hk2, hc⟩, fun hc => hc.2⟩
      · exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc.1 hk2⟩
    rw [hk2band]
    tauto
  have hlenW : (rqsWalk G₀ (rqsY rq₁ rq₃ qs q₁') (M.cpring.map fun x => h (M.icpY x))).length
      = (rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpY.cpring.map h)).length := by
    rw [hWold, hWnew]
    simp only [List.length_append, Hypermap.length_walkq, hflen]
    have h1 : (if rq₁.isKernel = true then [h (M.icpY (M.map.node M.point))] else []).length
        = (if rq₁.isKernel = true then [h (M.ecpY.map.node .X)] else []).length := by
      split_ifs <;> rfl
    have h2 : (if rq₂.isKernel = true then [h (.X : M.ecpY.Dart)] else []).length
        = (if rq₂.isKernel = true then 1 else 0) := by
      split_ifs <;> rfl
    rw [h1, h2]
    omega
  have hbandFull : ∀ u, G₀.Fband
        (rqsWalk G₀ (rqsY rq₁ rq₃ qs q₁') (M.cpring.map fun x => h (M.icpY x)) ++ r₀) u
      ↔ G₀.Fband (rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpY.cpring.map h) ++ r₀) u := by
    intro u
    rw [Hypermap.fband_append, Hypermap.fband_append, hbandW u]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr]
    exact ⟨hA1, hq1', hA3, hqu3, hfit1⟩
  · intro u hu hnr hnb
    by_cases hcu : G₀.CFace u (h (.X : M.ecpY.Dart))
    · cases hk2 : rq₂.isKernel
      · have hbad : ¬ BadRingArity rq₂.outerArity := not_badRingArity_of_cfquizY hk2 hne
        refine goodRingArity_of_not_badRingArity G₀ u ?_
        have harity : G₀.arity u = rq₂.outerArity + 2 := by
          rw [Hypermap.arity_cface _ hcu, hA2]
        rw [harity]
        simpa using hbad
      · exfalso
        obtain ⟨-, -, hdisj⟩ := Hypermap.simple_append.mp hq.simple
        refine hdisj (h (.X : M.ecpY.Dart)) ?_ ⟨u, hu, hcu.symm⟩
        rw [hWold]
        refine List.mem_append_right _ (List.mem_append_right _ ?_)
        refine List.mem_append_left _ ?_
        rw [ite_eq_left hk2]
        exact List.mem_cons_self
    · have hnbY : ¬ G₀.Fband (M.ecpY.cpring.map h) u := by
        rw [hmapY]
        intro hc
        rcases Hypermap.fband_cons.mp hc with hc1 | hc
        · exact hnb (by rw [hmap1]; exact Hypermap.fband_cons.mpr (Or.inl (hc1.trans hfaceY)))
        rcases Hypermap.fband_cons.mp hc with hc1 | hc
        · exact hcu hc1
        · exact hnb (by rw [hmap1]; exact Hypermap.fband_cons.mpr (Or.inr hc))
      have hnrY : u ∉ Set.range h := by
        rcases (hP u).mpr (Or.inl hnr) with hc | hc
        · exact hc
        · exact absurd hc hnbY
      exact hq.ringArity u hu hnrY hnbY
  · exact (Hypermap.simple_iff_of_fband_eq hbandFull (by simp [hlenW])).mpr hq.simple
  · intro u
    rw [hbandFull u, hq.cover u, hP u]


/-! #### Geometry of an `H` step

An `H` step adds three darts; the lemmas below locate them and compute the node
steps that link the two new ring questions to the ones they replace. -/

/-- The ring of an `H` step, with its head computed. -/
private theorem cpring_ecpH_eq (M : PointedMap) (hp : M.Proper) :
    M.ecpH.cpring
      = (.icp (.icp .Xe) : M.ecpH.Dart) :: .X :: (M.cpring.drop 2).map M.icpH := by
  rw [PointedMap.cpring_ecpH' M hp, PointedMap.node_ecpH M hp]
  rfl

/-- The image of an old dart is never one of the three darts an `H` step
adds. -/
private theorem icpH_ne_icp_icp_Xe (M : PointedMap) (y : M.Dart) :
    (M.icpH y : EcpDart (EcpDart (EcpDart M.Dart))) ≠ .icp (.icp .Xe) := by
  intro hc
  injection hc with h1
  injection h1 with h2
  injection h2

/-- The image of an old dart is never the new dart of an `H` step. -/
private theorem icpH_ne_X (M : PointedMap) (y : M.Dart) :
    (M.icpH y : EcpDart (EcpDart (EcpDart M.Dart))) ≠ .X := by
  intro hc
  injection hc

/-- The image of an old dart is never the dart after the new one. -/
private theorem icpH_ne_icp_X (M : PointedMap) (y : M.Dart) :
    (M.icpH y : EcpDart (EcpDart (EcpDart M.Dart))) ≠ .icp .X := by
  intro hc
  injection hc with h1
  injection h1

/-- **Every dart of an `H` step** is either an old dart, or lies on the face of
the new dart, of `x₀`, of `node x₀`, or of `node⁻¹ x₀`. -/
private theorem ecpH_dart_cases (M : PointedMap) (hp : M.Proper)
    (x : EcpDart (EcpDart (EcpDart M.Dart))) :
    (∃ y : M.Dart, x = M.icpH y) ∨ M.ecpH.map.CFace (.X : M.ecpH.Dart) x
      ∨ M.ecpH.map.CFace x (M.icpH M.point)
      ∨ M.ecpH.map.CFace x (M.icpH (M.map.node M.point))
      ∨ M.ecpH.map.CFace x (M.icpH (M.map.node⁻¹ M.point)) := by
  have hb2 : M.ecpY.map.CFace (M.ecpY.map.node⁻¹ (M.ecpY.map.node⁻¹ .X))
      (M.icpY (M.map.node⁻¹ M.point)) := Hypermap.cface_b2_ecpY M.map M.point hp
  cases x with
  | X => exact Or.inr (Or.inl (Equiv.Perm.SameCycle.refl _ _))
  | Xe =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    exact (Hypermap.cface_Xe_icpN M.ecpY.map .X (.icp (.icp (M.map.node⁻¹ M.point)))).mpr
      hb2.symm
  | icp w =>
    cases w with
    | X => exact Or.inr (Or.inl ((PointedMap.cface_ecpH M hp _).mpr (Or.inr (Or.inl rfl))))
    | Xe =>
      refine Or.inr (Or.inr (Or.inl ?_))
      exact (Hypermap.cface_icpN M.ecpY.map .X .Xe (.icp (.icp M.point))).mpr
        (Hypermap.cface_Xe_ecpY M.map M.point hp)
    | icp v =>
      cases v with
      | X =>
        exact Or.inr (Or.inl ((PointedMap.cface_ecpH M hp _).mpr (Or.inr (Or.inr rfl))))
      | Xe =>
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        exact (Hypermap.cface_icpN M.ecpY.map .X (.icp .Xe)
          (.icp (.icp (M.map.node M.point)))).mpr (Hypermap.cface_icpXe_ecpY M.map M.point)
      | icp y => exact Or.inl ⟨y, rfl⟩

/-- The node of an old dart after an `N` step, away from the two darts the step
attaches to. -/
private theorem node_ecpN_icp {D : Type*} [Finite D] [DecidableEq D] (G : Hypermap D)
    (x₀ y : D) (h1 : y ≠ x₀) (h2 : G.node (G.node y) ≠ x₀) :
    (Hypermap.ecpNMap G x₀).node (.icp y) = .icp (G.node y) := by
  have hu : (Hypermap.ecpNMap G x₀).node (.icp y)
      = if y = x₀ then .Xe else if G.node (G.node y) = x₀ then .X else .icp (G.node y) := rfl
  rw [hu, ite_eq_right h1, ite_eq_right h2]

/-- The node of the image of `node x₀` after an `H` step. -/
private theorem node_icpH_node (M : PointedMap) :
    M.ecpH.map.node (M.icpH (M.map.node M.point)) = (.icp (.icp .X) : M.ecpH.Dart) := by
  have h1 : M.ecpY.map.node (M.icpY (M.map.node M.point)) = (.icp .X : M.ecpY.Dart) :=
    node_icpY_node M
  have h2 : M.ecpY.map.node (.icp .X : M.ecpY.Dart) = (.Xe : M.ecpY.Dart) := node_icp_X_ecpY M
  have hne1 : (M.icpY (M.map.node M.point) : M.ecpY.Dart) ≠ .X := icpY_ne_X M _
  have hne2 : M.ecpY.map.node (M.ecpY.map.node (M.icpY (M.map.node M.point)))
      ≠ (.X : M.ecpY.Dart) := by
    rw [h1, h2]
    intro hc
    exact absurd (show (EcpDart.Xe : EcpDart (EcpDart M.Dart)) = .X from hc) (by simp)
  have hkey : M.ecpH.map.node (M.icpH (M.map.node M.point))
      = EcpDart.icp (M.ecpY.map.node (M.icpY (M.map.node M.point))) :=
    node_ecpN_icp M.ecpY.map .X (M.icpY (M.map.node M.point)) hne1 hne2
  rw [hkey, h1]

/-- The node of the image of `x₀` after an `H` step. -/
private theorem node_icpH_point (M : PointedMap) (hp : M.Proper) :
    M.ecpH.map.node (M.icpH M.point) = (.icp .X : M.ecpH.Dart) := by
  have h1 : M.ecpY.map.node (M.icpY M.point) = (.X : M.ecpY.Dart) := by
    have := Hypermap.node_inv_ecpY_X M.map M.point hp
    exact (Equiv.Perm.inv_eq_iff_eq.mp this).symm
  have h2 : M.ecpY.map.node (.X : M.ecpY.Dart) = (.icp .Xe : M.ecpY.Dart) :=
    PointedMap.node_ecpY M
  have hne1 : (M.icpY M.point : M.ecpY.Dart) ≠ .X := icpY_ne_X M _
  have hne2 : M.ecpY.map.node (M.ecpY.map.node (M.icpY M.point)) ≠ (.X : M.ecpY.Dart) := by
    rw [h1, h2]
    intro hc
    exact absurd (show (EcpDart.icp EcpDart.Xe : EcpDart (EcpDart M.Dart)) = .X from hc)
      (by simp)
  have hkey : M.ecpH.map.node (M.icpH M.point)
      = EcpDart.icp (M.ecpY.map.node (M.icpY M.point)) :=
    node_ecpN_icp M.ecpY.map .X (M.icpY M.point) hne1 hne2
  rw [hkey, h1]

/-- The node of the dart just after the image of `x₀` in an `H` step. -/
private theorem node_icp_X_ecpH (M : PointedMap) :
    M.ecpH.map.node (.icp .X : M.ecpH.Dart) = (.Xe : M.ecpH.Dart) := rfl

/-- One node step back from the image of `node x₀` reaches the node of the new
dart. -/
private theorem edge_node_icpH_node (M : PointedMap) (hp : M.Proper) :
    M.ecpH.map.edge (M.ecpH.map.node (M.icpH (M.map.node M.point)))
      = M.ecpH.map.node .X := by
  rw [node_icpH_node, PointedMap.node_ecpH M hp]
  rfl

/-- Two node steps back from the image of `x₀` reach the new dart. -/
private theorem edge_node_node_icpH_point (M : PointedMap) (hp : M.Proper) :
    M.ecpH.map.edge (M.ecpH.map.node (M.ecpH.map.node (M.icpH M.point)))
      = (.X : M.ecpH.Dart) := by
  rw [node_icpH_point M hp, node_icp_X_ecpH]
  rfl

/-- The new dart of an `H` step and the dart on the node of the image of
`node x₀` lie on the same face. -/
private theorem cface_icp_icp_X_ecpH (M : PointedMap) (hp : M.Proper) :
    M.ecpH.map.CFace (.icp (.icp .X) : M.ecpH.Dart) .X :=
  ((PointedMap.cface_ecpH M hp _).mpr (Or.inr (Or.inr rfl))).symm

/-- The image of `node x₀` is not on the ring of an `H` step. -/
private theorem not_mem_cpring_icpH_node (M : PointedMap) (hp : M.Proper) :
    M.icpH (M.map.node M.point) ∉ M.ecpH.cpring := by
  rw [cpring_ecpH_eq M hp]
  intro hc
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (M.icpH (M.map.node M.point) : EcpDart (EcpDart (EcpDart M.Dart)))
      = .icp (.icp .Xe) from h1) (icpH_ne_icp_icp_Xe M _)
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (M.icpH (M.map.node M.point) : EcpDart (EcpDart (EcpDart M.Dart)))
      = .X from h1) (icpH_ne_X M _)
  obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hc
  have hy' : y = M.map.node M.point :=
    PointedMap.icpH_injective M
      (show (M.icpH y : EcpDart (EcpDart (EcpDart M.Dart)))
        = M.icpH (M.map.node M.point) from hyeq)
  subst hy'
  have hnd : (M.map.node M.point :: M.point :: M.cpring.drop 2).Nodup := by
    rw [← head_proper_cpring_pointed M hp]
    exact nodup_cpring_pointed M
  exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hy)

/-- The image of `x₀` is not on the ring of an `H` step. -/
private theorem not_mem_cpring_icpH_point (M : PointedMap) (hp : M.Proper) :
    M.icpH M.point ∉ M.ecpH.cpring := by
  rw [cpring_ecpH_eq M hp]
  intro hc
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (M.icpH M.point : EcpDart (EcpDart (EcpDart M.Dart)))
      = .icp (.icp .Xe) from h1) (icpH_ne_icp_icp_Xe M _)
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (M.icpH M.point : EcpDart (EcpDart (EcpDart M.Dart)))
      = .X from h1) (icpH_ne_X M _)
  obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hc
  have hy' : y = M.point :=
    PointedMap.icpH_injective M
      (show (M.icpH y : EcpDart (EcpDart (EcpDart M.Dart))) = M.icpH M.point from hyeq)
  subst hy'
  have hnd : (M.map.node M.point :: M.point :: M.cpring.drop 2).Nodup := by
    rw [← head_proper_cpring_pointed M hp]
    exact nodup_cpring_pointed M
  exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hy

/-- The dart just after the image of `x₀` is not on the ring of an `H` step. -/
private theorem not_mem_cpring_icp_X_ecpH (M : PointedMap) (hp : M.Proper) :
    (.icp .X : M.ecpH.Dart) ∉ M.ecpH.cpring := by
  rw [cpring_ecpH_eq M hp]
  intro hc
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (EcpDart.icp EcpDart.X : EcpDart (EcpDart (EcpDart M.Dart)))
      = .icp (.icp .Xe) from h1) (by intro hh; injection hh with hh1; injection hh1)
  rcases List.mem_cons.mp hc with h1 | hc
  · exact absurd (show (EcpDart.icp EcpDart.X : EcpDart (EcpDart (EcpDart M.Dart)))
      = .X from h1) (by intro hh; injection hh)
  obtain ⟨y, -, hy⟩ := List.mem_map.mp hc
  exact absurd (show (M.icpH y : EcpDart (EcpDart (EcpDart M.Dart)))
    = .icp .X from hy) (icpH_ne_icp_X M y)


/-- A successful `H` step at a ring dart passes the ring arity check. -/
theorem not_badRingArity_of_cfquizH {rq₁ rq₂ : RingQuestion}
    {k : Question → Question → List RingQuestion} (hk : rq₂.isKernel = false)
    (hne : cfquizH rq₁ rq₂ k ≠ []) : ¬ BadRingArity (rq₂.outerArity + 1) := by
  intro hb
  have hk' : ¬ (rq₂.isKernel = true) := by simp [hk]
  exact hne (by rw [cfquizH, ite_eq_right hk', ite_eq_left hb])

/-- **The five shapes an `H` step can handle.** -/
theorem cfquizH_cases {rq₁ rq₂ : RingQuestion} {k : Question → Question → List RingQuestion}
    (hne : cfquizH rq₁ rq₂ k ≠ []) :
    (rq₂.isKernel = false ∧ rq₁.question = .ask0 ∧ rq₂.question = .ask0
        ∧ cfquizH rq₁ rq₂ k = k .ask0 .ask0)
      ∨ (rq₂.isKernel = true ∧ rq₁.question = .ask0 ∧ rq₂.question = .ask0
        ∧ cfquizH rq₁ rq₂ k = k (.ask1 (smallQArity (rq₂.outerArity + 1))) .ask0)
      ∨ (rq₂.isKernel = true ∧ rq₁.question = .ask0 ∧ rq₂.question = .ask0
        ∧ cfquizH rq₁ rq₂ k = k .ask0 (.ask1 (smallQArity (rq₂.outerArity + 1))))
      ∨ (rq₂.isKernel = true ∧ rq₁.question = .ask0
        ∧ cfquizH rq₁ rq₂ k
            = k .ask0 (.askL (smallQArity (rq₂.outerArity + 1)) rq₂.question))
      ∨ (rq₂.isKernel = true ∧ rq₂.question = .ask0
        ∧ cfquizH rq₁ rq₂ k
            = k (.askR (smallQArity (rq₂.outerArity + 1)) rq₁.question) .ask0) := by
  by_cases hk : rq₂.isKernel = true
  · have hb : ¬ BadSmallArity (smallQArity (rq₂.outerArity + 1)) := by
      intro hb
      exact hne (by rw [cfquizH, ite_eq_left hk, ite_eq_left hb])
    have heq : cfquizH rq₁ rq₂ k = (match rq₁.question, rq₂.question, rq₁.isKernel with
        | .ask0, .ask0, true => k (.ask1 (smallQArity (rq₂.outerArity + 1))) .ask0
        | .ask0, .ask0, false => k .ask0 (.ask1 (smallQArity (rq₂.outerArity + 1)))
        | .ask0, q₂, _ => k .ask0 (.askL (smallQArity (rq₂.outerArity + 1)) q₂)
        | q₁, .ask0, _ => k (.askR (smallQArity (rq₂.outerArity + 1)) q₁) .ask0
        | _, _, _ => []) := by
      rw [cfquizH, ite_eq_left hk, ite_eq_right hb]
    cases hq1 : rq₁.question
    case ask0 =>
      cases hq2 : rq₂.question
      case ask0 =>
        cases hk1 : rq₁.isKernel
        · exact Or.inr (Or.inr (Or.inl ⟨hk, rfl, rfl, by rw [heq, hq1, hq2, hk1]⟩))
        · exact Or.inr (Or.inl ⟨hk, rfl, rfl, by rw [heq, hq1, hq2, hk1]⟩)
      all_goals exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, rfl, by rw [heq, hq1, hq2]⟩)))
    all_goals
      cases hq2 : rq₂.question
      case ask0 =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hk, rfl, by rw [heq, hq1, hq2]⟩)))
      all_goals exact absurd (by rw [heq, hq1, hq2]) hne
  · have hk' : rq₂.isKernel = false := by simpa using hk
    have hb : ¬ BadRingArity (rq₂.outerArity + 1) := not_badRingArity_of_cfquizH hk' hne
    have heq : cfquizH rq₁ rq₂ k = (match rq₁.question, rq₂.question with
        | .ask0, .ask0 => k .ask0 .ask0
        | _, _ => []) := by
      rw [cfquizH, ite_eq_right hk, ite_eq_right hb]
    cases hq1 : rq₁.question
    case ask0 =>
      cases hq2 : rq₂.question
      case ask0 => exact Or.inl ⟨hk', rfl, rfl, by rw [heq, hq1, hq2]⟩
      all_goals exact absurd (by rw [heq, hq1, hq2]) hne
    all_goals
      cases hq2 : rq₂.question <;> exact absurd (by rw [heq, hq1, hq2]) hne


/-- **An `H` step preserves the invariant**: the new hub face is detached from
the ring, and the two new ring questions split the work of the two questions of
the ring darts the step removes. -/
theorem rqsProper_H {D₀ : Type*} [Finite D₀] (G₀ : Hypermap D₀) (r₀ : List D₀)
    (M : PointedMap) (hlong : M.Long) (hUr : M.map.Simple M.cpring)
    (h : M.ecpH.Dart → D₀) (hinj : Function.Injective h)
    (hE : ∀ x, h (M.ecpH.map.edge x) = G₀.edge (h x))
    (hN : ∀ x, x ∉ M.ecpH.cpring → h (M.ecpH.map.node x) = G₀.node (h x))
    (hF : ∀ x y, G₀.CFace (h x) (h y) ↔ M.ecpH.map.CFace x y)
    (rq₁ rq₂ rq₃ : RingQuestion) (qs : List RingQuestion)
    (hq : RqsProper G₀ M.ecpH.map h r₀ M.ecpH.cpring (rq₁ :: rq₂ :: rq₃ :: qs))
    (hne : cfquizH rq₁ rq₂ (rqsH rq₁ rq₃ qs) ≠ []) :
    RqsProper G₀ M.map (fun x => h (M.icpH x)) r₀ M.cpring
      (cfquizH rq₁ rq₂ (rqsH rq₁ rq₃ qs)) := by
  have hp : M.Proper := PointedMap.Long.proper hlong
  have hr : M.cpring = M.map.node M.point :: M.point :: M.map.node⁻¹ M.point
      :: M.cpring.drop 3 := by
    have hl := Hypermap.head_long_cpring hlong
    rwa [Hypermap.face_edge] at hl
  have hdrop2 : M.cpring.drop 2 = M.map.node⁻¹ M.point :: M.cpring.drop 3 := by
    conv_lhs => rw [hr]
    rfl
  have hringH : M.ecpH.cpring = M.ecpH.map.node .X :: (.X : M.ecpH.Dart)
      :: M.icpH (M.map.node⁻¹ M.point) :: (M.cpring.drop 3).map M.icpH := by
    rw [PointedMap.cpring_ecpH' M hp, hdrop2, List.map_cons]
  -- simplicity of the old ring
  have hUr3 : M.map.Simple (M.map.node M.point :: M.point :: M.map.node⁻¹ M.point
      :: M.cpring.drop 3) := hr ▸ hUr
  have hb1 := hUr3.not_fband
  have hb2 := hUr3.of_cons.not_fband
  have hb3 := hUr3.of_cons.of_cons.not_fband
  have hnpt_pt : ¬ M.map.CFace (M.map.node M.point) M.point := fun hc =>
    hb1 ⟨M.point, List.mem_cons_self, hc⟩
  have hnpt_ipt : ¬ M.map.CFace (M.map.node M.point) (M.map.node⁻¹ M.point) := fun hc =>
    hb1 ⟨M.map.node⁻¹ M.point, List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
  have hpt_ipt : ¬ M.map.CFace M.point (M.map.node⁻¹ M.point) := fun hc =>
    hb2 ⟨M.map.node⁻¹ M.point, List.mem_cons_self, hc⟩
  have hx_npt : ∀ x ∈ M.cpring.drop 3, ¬ M.map.CFace x (M.map.node M.point) := fun x hx hc =>
    hb1 ⟨x, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx), hc.symm⟩
  have hx_pt : ∀ x ∈ M.cpring.drop 3, ¬ M.map.CFace x M.point := fun x hx hc =>
    hb2 ⟨x, List.mem_cons_of_mem _ hx, hc.symm⟩
  have hx_ipt : ∀ x ∈ M.cpring.drop 3, ¬ M.map.CFace x (M.map.node⁻¹ M.point) :=
    fun x hx hc => hb3 ⟨x, hx, hc.symm⟩
  -- arities
  have hAu0 : M.ecpH.map.arity (.X : M.ecpH.Dart) = 3 := arity_ecpH_X M hp
  have hAv1 : M.ecpH.map.arity (M.icpH (M.map.node M.point))
      = M.map.arity (M.map.node M.point) + 1 :=
    arity_icpH_of_node M hp (Equiv.Perm.SameCycle.refl _ _) hnpt_pt hnpt_ipt
  have hAv2 : M.ecpH.map.arity (M.icpH M.point) = M.map.arity M.point + 1 :=
    arity_icpH_of_point M hp (fun hc => hnpt_pt hc.symm)
      (Equiv.Perm.SameCycle.refl _ _) hpt_ipt
  have hAv3 : M.ecpH.map.arity (M.icpH (M.map.node⁻¹ M.point))
      = M.map.arity (M.map.node⁻¹ M.point) + 1 :=
    arity_icpH_of_node_inv M hp (fun hc => hnpt_ipt hc.symm) (fun hc => hpt_ipt hc.symm)
      (Equiv.Perm.SameCycle.refl _ _)
  have hAr1 : ∀ x ∈ M.cpring.drop 3, M.ecpH.map.arity (M.icpH x) = M.map.arity x :=
    fun x hx => arity_icpH_of_not M hp (hx_npt x hx) (hx_pt x hx) (hx_ipt x hx)
  have hnu0F : M.ecpH.map.CFace (M.ecpH.map.node .X) (M.icpH (M.map.node M.point)) :=
    PointedMap.cface_node_ecpH' M hp
  have hAnu0 : M.ecpH.map.arity (M.ecpH.map.node (.X : M.ecpH.Dart))
      = M.map.arity (M.map.node M.point) + 1 := by
    rw [Hypermap.arity_cface _ hnu0F, hAv1]
  -- the fit of the old ring questions
  have hfitH : rqsFit G₀ M.ecpH.map h (rq₁ :: rq₂ :: rq₃ :: qs)
      (M.ecpH.map.node .X :: (.X : M.ecpH.Dart) :: M.icpH (M.map.node⁻¹ M.point)
        :: (M.cpring.drop 3).map M.icpH) := by
    rw [← hringH]
    exact hq.fit
  obtain ⟨Ea1, hqu1, Ea2, hqu2, Ea3, hqu3, hqr1⟩ := hfitH
  have hfit1 : rqsFit G₀ M.map (fun x => h (M.icpH x)) qs (M.cpring.drop 3) :=
    (rqsFit_map_iff G₀ M.map M.ecpH.map h M.icpH qs (M.cpring.drop 3) hAr1).mp hqr1
  have hfaceH : G₀.CFace (h (M.ecpH.map.node .X)) (h (M.icpH (M.map.node M.point))) :=
    (hF _ _).mpr hnu0F
  have hA1 : G₀.arity (h (M.icpH (M.map.node M.point)))
      = (rq₁.outerArity + 1) + M.map.arity (M.map.node M.point) := by
    rw [← Hypermap.arity_cface _ hfaceH, Ea1, hAnu0]
    omega
  have hA3 : G₀.arity (h (M.icpH (M.map.node⁻¹ M.point)))
      = (rq₃.outerArity + 1) + M.map.arity (M.map.node⁻¹ M.point) := by
    rw [Ea3, hAv3]
    omega
  have hA2 : G₀.arity (h (.X : M.ecpH.Dart)) = rq₂.outerArity + 3 := by rw [Ea2, hAu0]
  -- the mapped rings
  have hmap1 : M.cpring.map (fun x => h (M.icpH x))
      = h (M.icpH (M.map.node M.point)) :: h (M.icpH M.point)
        :: h (M.icpH (M.map.node⁻¹ M.point))
          :: ((M.cpring.drop 3).map fun x => h (M.icpH x)) := by
    rw [hr]
    rfl
  have hmapH : M.ecpH.cpring.map h
      = h (M.ecpH.map.node .X) :: h (.X : M.ecpH.Dart) :: h (M.icpH (M.map.node⁻¹ M.point))
        :: ((M.cpring.drop 3).map fun x => h (M.icpH x)) := by
    rw [hringH]
    have hcons : List.map h (M.ecpH.map.node .X :: (.X : M.ecpH.Dart)
        :: M.icpH (M.map.node⁻¹ M.point) :: (M.cpring.drop 3).map M.icpH)
        = h (M.ecpH.map.node .X) :: h (.X : M.ecpH.Dart)
          :: h (M.icpH (M.map.node⁻¹ M.point))
            :: (((M.cpring.drop 3).map M.icpH).map h) := rfl
    rw [hcons, List.map_map]
    rfl
  -- the face of `x₀` is detached from the ring by the step
  have hv2ring : ¬ G₀.Fband (M.ecpH.cpring.map h) (h (M.icpH M.point)) := by
    rw [hmapH]
    intro hc
    rcases Hypermap.fband_cons.mp hc with hc1 | hc
    · exact hnpt_pt
        ((PointedMap.cface_icpH' M _ _).mp ((hF _ _).mp (hc1.trans hfaceH))).symm
    rcases Hypermap.fband_cons.mp hc with hc1 | hc
    · exact PointedMap.not_cface_ecpH_icpH M hp M.point ((hF _ _).mp hc1).symm
    rcases Hypermap.fband_cons.mp hc with hc1 | hc
    · exact hpt_ipt ((PointedMap.cface_icpH' M _ _).mp ((hF _ _).mp hc1))
    · obtain ⟨v, hv, hcv⟩ := hc
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact hx_pt x hx ((PointedMap.cface_icpH' M _ _).mp ((hF _ _).mp hcv)).symm
  have hv2band : ¬ G₀.Fband
      (rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpH.cpring.map h) ++ r₀)
      (h (M.icpH M.point)) := by
    intro hc
    rcases (hq.cover _).mp hc with hc1 | hc1
    · exact hc1 ⟨M.icpH M.point, rfl⟩
    · exact hv2ring hc1
  have hrange2 : ∀ u, G₀.CFace (h (M.icpH M.point)) u → u ∈ Set.range h := by
    intro u hcu
    by_contra hnr
    exact hv2band ((Hypermap.Fband.congr hcu).mpr ((hq.cover u).mpr (Or.inl hnr)))
  have hAv2G : G₀.arity (h (M.icpH M.point)) = M.ecpH.map.arity (M.icpH M.point) := by
    have hmem : ∀ u, u ∈ (orbitList M.ecpH.map.face (M.icpH M.point)).map h
        ↔ G₀.CFace (h (M.icpH M.point)) u := by
      intro u
      constructor
      · intro hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
        exact (hF _ _).mpr (mem_orbitList.mp hw)
      · intro hu
        obtain ⟨w, rfl⟩ := hrange2 u hu
        exact List.mem_map.mpr ⟨w, mem_orbitList.mpr ((hF _ _).mp hu), rfl⟩
    have hnd : ((orbitList M.ecpH.map.face (M.icpH M.point)).map h).Nodup :=
      List.Nodup.map hinj (nodup_orbitList _ _)
    rw [arity_eq_length (G := G₀) hnd hmem, List.length_map, length_orbitList]
    rfl
  have hA2' : G₀.arity (h (M.icpH M.point)) = 1 + M.map.arity M.point := by
    rw [hAv2G, hAv2]
    omega
  -- the node steps
  have hnv1 : G₀.node (h (M.icpH (M.map.node M.point)))
      = h (M.ecpH.map.node (M.icpH (M.map.node M.point))) :=
    (hN _ (not_mem_cpring_icpH_node M hp)).symm
  have hen1 : G₀.edge (G₀.node (h (M.icpH (M.map.node M.point))))
      = h (M.ecpH.map.node (.X : M.ecpH.Dart)) := by
    rw [hnv1, ← hE, edge_node_icpH_node M hp]
  have hqR : G₀.qstepR (G₀.node (h (M.icpH (M.map.node M.point))))
      = G₀.node (h (M.ecpH.map.node .X)) := by rw [Hypermap.qstepR, hen1]
  have hnv1F : G₀.CFace (G₀.node (h (M.icpH (M.map.node M.point))))
      (h (.X : M.ecpH.Dart)) := by
    rw [hnv1, node_icpH_node]
    exact (hF _ _).mpr (cface_icp_icp_X_ecpH M hp)
  have hnv2 : G₀.node (h (M.icpH M.point)) = h (M.ecpH.map.node (M.icpH M.point)) :=
    (hN _ (not_mem_cpring_icpH_point M hp)).symm
  have hnn2 : G₀.node (G₀.node (h (M.icpH M.point)))
      = h (M.ecpH.map.node (.icp .X : M.ecpH.Dart)) := by
    rw [hnv2, node_icpH_point M hp, hN _ (not_mem_cpring_icp_X_ecpH M hp)]
  have henn2 : G₀.edge (G₀.node (G₀.node (h (M.icpH M.point)))) = h (.X : M.ecpH.Dart) := by
    rw [hnn2, ← hE, node_icp_X_ecpH]
    rfl
  have hqL2 : G₀.qstepL (G₀.node (h (M.icpH M.point))) = G₀.node (h (.X : M.ecpH.Dart)) := by
    rw [Hypermap.qstepL, henn2]
  have hfaceu0 : G₀.face (h (.X : M.ecpH.Dart)) = G₀.node (h (M.icpH M.point)) := by
    rw [← henn2, Hypermap.face_edge, Hypermap.inv_node_node]
  have hnv2F : G₀.CFace (G₀.node (h (M.icpH M.point))) (h (.X : M.ecpH.Dart)) := by
    rw [← hfaceu0]
    exact (G₀.cface_face _).symm
  have hAnv1 : G₀.arity (G₀.node (h (M.icpH (M.map.node M.point))))
      = rq₂.outerArity + 3 := by
    rw [Hypermap.arity_cface _ hnv1F, hA2]
  have hAnv2 : G₀.arity (G₀.node (h (M.icpH M.point))) = rq₂.outerArity + 3 := by
    rw [Hypermap.arity_cface _ hnv2F, hA2]
  -- the covered faces
  have hP : ∀ u, (G₀.CFace u (h (M.icpH M.point))
        ∨ (u ∉ Set.range h ∨ G₀.Fband (M.ecpH.cpring.map h) u))
      ↔ (u ∉ Set.range (fun x => h (M.icpH x))
          ∨ G₀.Fband (M.cpring.map fun x => h (M.icpH x)) u) := by
    intro u
    rw [hmap1, hmapH]
    constructor
    · rintro (hc | hu | hu)
      · exact Or.inr (Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inl hc))))
      · exact Or.inl fun ⟨x, hx⟩ => hu ⟨M.icpH x, hx⟩
      · rcases Hypermap.fband_cons.mp hu with hc | hu
        · exact Or.inr (Hypermap.fband_cons.mpr (Or.inl (hc.trans hfaceH)))
        rcases Hypermap.fband_cons.mp hu with hc | hu
        · refine Or.inl ?_
          rintro ⟨z, rfl⟩
          exact absurd ((hF _ _).mp hc).symm (PointedMap.not_cface_ecpH_icpH M hp z)
        · exact Or.inr (Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr
            (Or.inr hu))))
    · rintro (hu | hu)
      · by_cases hx : u ∈ Set.range h
        · obtain ⟨x, rfl⟩ := hx
          rcases ecpH_dart_cases M hp x with ⟨y, rfl⟩ | hc | hc | hc | hc
          · exact absurd ⟨y, rfl⟩ hu
          · exact Or.inr (Or.inr (Hypermap.fband_cons.mpr (Or.inr
              (Hypermap.fband_cons.mpr (Or.inl ((hF _ _).mpr hc).symm)))))
          · exact Or.inl ((hF _ _).mpr hc)
          · exact Or.inr (Or.inr (Hypermap.fband_cons.mpr
              (Or.inl (((hF _ _).mpr hc).trans hfaceH.symm))))
          · exact Or.inr (Or.inr (Hypermap.fband_cons.mpr (Or.inr
              (Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr
                (Or.inl ((hF _ _).mpr hc))))))))
        · exact Or.inr (Or.inl hx)
      · rcases Hypermap.fband_cons.mp hu with hc | hu
        · exact Or.inr (Or.inr (Hypermap.fband_cons.mpr (Or.inl (hc.trans hfaceH.symm))))
        rcases Hypermap.fband_cons.mp hu with hc | hu
        · exact Or.inl hc
        · exact Or.inr (Or.inr (Hypermap.fband_cons.mpr (Or.inr
            (Hypermap.fband_cons.mpr (Or.inr hu)))))
  suffices H : ∀ q₁' q₂' : Question,
      G₀.Fitq (G₀.node (h (M.icpH (M.map.node M.point)))) q₁' →
      G₀.Fitq (G₀.node (h (M.icpH M.point))) q₂' →
      (∀ u, (G₀.Fband (G₀.walkq (G₀.node (h (M.icpH (M.map.node M.point)))) q₁') u
          ∨ G₀.Fband (G₀.walkq (G₀.node (h (M.icpH M.point))) q₂') u) ↔
        (G₀.Fband (G₀.walkq (G₀.node (h (M.ecpH.map.node .X))) rq₁.question) u
          ∨ (rq₂.isKernel = true ∧ G₀.CFace u (h (.X : M.ecpH.Dart)))
          ∨ G₀.Fband (G₀.walkq (G₀.node (h (.X : M.ecpH.Dart))) rq₂.question) u)) →
      q₁'.flat.length + q₂'.flat.length = rq₁.question.flat.length
        + (if rq₂.isKernel = true then 1 else 0) + rq₂.question.flat.length →
      RqsProper G₀ M.map (fun x => h (M.icpH x)) r₀ M.cpring (rqsH rq₁ rq₃ qs q₁' q₂') by
    have hqa : rq₂.isKernel = true →
        (smallQArity (rq₂.outerArity + 1)).toNat = rq₂.outerArity + 3 := by
      intro hk
      have hb : ¬ BadSmallArity (smallQArity (rq₂.outerArity + 1)) := by
        intro hb
        exact hne (by rw [cfquizH, ite_eq_left hk, ite_eq_left hb])
      have h2 : (smallQArity (rq₂.outerArity + 1)).toNat = (rq₂.outerArity + 1) + 2 := by
        by_contra hc
        exact hb ((badSmallArity_smallQArity _).mpr hc)
      omega
    rcases cfquizH_cases hne with ⟨hk, h1, h2, heq⟩ | ⟨hk, h1, h2, heq⟩
      | ⟨hk, h1, h2, heq⟩ | ⟨hk, h1, heq⟩ | ⟨hk, h2, heq⟩
    · rw [heq]
      refine H .ask0 .ask0 rfl rfl (fun u => ?_) ?_
      · rw [walkq_ask0, walkq_ask0, h1, h2, walkq_ask0, walkq_ask0]
        constructor
        · rintro (hc | hc) <;> exact absurd hc (by simp)
        · rintro (hc | ⟨hc, -⟩ | hc)
          · exact absurd hc (by simp)
          · exact absurd hc (by simp [hk])
          · exact absurd hc (by simp)
      · rw [h1, h2, ite_eq_right (show ¬ (rq₂.isKernel = true) by simp [hk])]
        simp only [flat_ask0, List.length_nil]
    · rw [heq]
      refine H (.ask1 (smallQArity (rq₂.outerArity + 1))) .ask0 ?_ rfl (fun u => ?_) ?_
      · change (Question.ask1 _).flat = _
        rw [walkq_ask1, flat_ask1, List.map_cons, hAnv1, hqa hk]
        rfl
      · rw [walkq_ask1, walkq_ask0, h1, h2, walkq_ask0, walkq_ask0]
        constructor
        · rintro (hc | hc)
          · exact Or.inr (Or.inl ⟨hk, ((fband_singleton _ _).mp hc).trans hnv1F⟩)
          · exact absurd hc (by simp)
        · rintro (hc | ⟨-, hc⟩ | hc)
          · exact absurd hc (by simp)
          · exact Or.inl ((fband_singleton _ _).mpr (hc.trans hnv1F.symm))
          · exact absurd hc (by simp)
      · rw [h1, h2, ite_eq_left hk]
        simp only [flat_ask0, flat_ask1, List.length_nil, List.length_cons]
    · rw [heq]
      refine H .ask0 (.ask1 (smallQArity (rq₂.outerArity + 1))) rfl ?_ (fun u => ?_) ?_
      · change (Question.ask1 _).flat = _
        rw [walkq_ask1, flat_ask1, List.map_cons, hAnv2, hqa hk]
        rfl
      · rw [walkq_ask0, walkq_ask1, h1, h2, walkq_ask0, walkq_ask0]
        constructor
        · rintro (hc | hc)
          · exact absurd hc (by simp)
          · exact Or.inr (Or.inl ⟨hk, ((fband_singleton _ _).mp hc).trans hnv2F⟩)
        · rintro (hc | ⟨-, hc⟩ | hc)
          · exact absurd hc (by simp)
          · exact Or.inr ((fband_singleton _ _).mpr (hc.trans hnv2F.symm))
          · exact absurd hc (by simp)
      · rw [h1, h2, ite_eq_left hk]
        simp only [flat_ask0, flat_ask1, List.length_nil, List.length_cons]
    · rw [heq]
      have hfitu2 : rq₂.question.flat
          = (G₀.walkq (G₀.node (h (.X : M.ecpH.Dart))) rq₂.question).map G₀.arity := hqu2
      have hw : G₀.walkq (G₀.node (h (M.icpH M.point)))
            (.askL (smallQArity (rq₂.outerArity + 1)) rq₂.question)
          = G₀.node (h (M.icpH M.point))
            :: G₀.walkq (G₀.node (h (.X : M.ecpH.Dart))) rq₂.question := by
        rw [walkq_askL, hqL2]
      refine H .ask0 (.askL (smallQArity (rq₂.outerArity + 1)) rq₂.question) rfl ?_
        (fun u => ?_) ?_
      · change (Question.askL _ _).flat = _
        rw [hw, flat_askL, List.map_cons, hAnv2, hqa hk, ← hfitu2]
      · rw [hw, walkq_ask0, h1, walkq_ask0]
        constructor
        · rintro (hc | hc)
          · exact absurd hc (by simp)
          · rcases Hypermap.fband_cons.mp hc with hc1 | hc1
            · exact Or.inr (Or.inl ⟨hk, hc1.trans hnv2F⟩)
            · exact Or.inr (Or.inr hc1)
        · rintro (hc | ⟨-, hc⟩ | hc)
          · exact absurd hc (by simp)
          · exact Or.inr (Hypermap.fband_cons.mpr (Or.inl (hc.trans hnv2F.symm)))
          · exact Or.inr (Hypermap.fband_cons.mpr (Or.inr hc))
      · rw [h1, ite_eq_left hk]
        simp only [flat_ask0, flat_askL, List.length_nil, List.length_cons]
        omega
    · rw [heq]
      have hfitu1 : rq₁.question.flat
          = (G₀.walkq (G₀.node (h (M.ecpH.map.node .X))) rq₁.question).map G₀.arity := hqu1
      have hw : G₀.walkq (G₀.node (h (M.icpH (M.map.node M.point))))
            (.askR (smallQArity (rq₂.outerArity + 1)) rq₁.question)
          = G₀.node (h (M.icpH (M.map.node M.point)))
            :: G₀.walkq (G₀.node (h (M.ecpH.map.node .X))) rq₁.question := by
        rw [walkq_askR, hqR]
      refine H (.askR (smallQArity (rq₂.outerArity + 1)) rq₁.question) .ask0 ?_ rfl
        (fun u => ?_) ?_
      · change (Question.askR _ _).flat = _
        rw [hw, flat_askR, List.map_cons, hAnv1, hqa hk, ← hfitu1]
      · rw [hw, walkq_ask0, h2, walkq_ask0]
        constructor
        · rintro (hc | hc)
          · rcases Hypermap.fband_cons.mp hc with hc1 | hc1
            · exact Or.inr (Or.inl ⟨hk, hc1.trans hnv1F⟩)
            · exact Or.inl hc1
          · exact absurd hc (by simp)
        · rintro (hc | ⟨-, hc⟩ | hc)
          · exact Or.inl (Hypermap.fband_cons.mpr (Or.inr hc))
          · exact Or.inl (Hypermap.fband_cons.mpr (Or.inl (hc.trans hnv1F.symm)))
          · exact absurd hc (by simp)
      · rw [h2, ite_eq_left hk]
        simp only [flat_ask0, flat_askR, List.length_nil, List.length_cons]
  intro q₁' q₂' hq1' hq2' hband hflen
  have hWold : rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpH.cpring.map h)
      = (if rq₁.isKernel = true then [h (M.ecpH.map.node .X)] else [])
        ++ (G₀.walkq (G₀.node (h (M.ecpH.map.node .X))) rq₁.question
          ++ ((if rq₂.isKernel = true then [h (.X : M.ecpH.Dart)] else [])
            ++ (G₀.walkq (G₀.node (h (.X : M.ecpH.Dart))) rq₂.question
              ++ rqsWalk G₀ (rq₃ :: qs)
                (h (M.icpH (M.map.node⁻¹ M.point))
                  :: ((M.cpring.drop 3).map fun x => h (M.icpH x)))))) := by
    rw [hmapH, rqsWalk_cons, rqsWalk_cons]
  have hWnew : rqsWalk G₀ (rqsH rq₁ rq₃ qs q₁' q₂') (M.cpring.map fun x => h (M.icpH x))
      = (if rq₁.isKernel = true then [h (M.icpH (M.map.node M.point))] else [])
        ++ (G₀.walkq (G₀.node (h (M.icpH (M.map.node M.point)))) q₁'
          ++ (h (M.icpH M.point) :: (G₀.walkq (G₀.node (h (M.icpH M.point))) q₂'
            ++ rqsWalk G₀ (rq₃ :: qs)
              (h (M.icpH (M.map.node⁻¹ M.point))
                :: ((M.cpring.drop 3).map fun x => h (M.icpH x)))))) := by
    have hstep : rqsWalk G₀ (RingQuestion.mk true 1 q₂'
          :: (RingQuestion.mk rq₃.isKernel (rq₃.outerArity + 1) rq₃.question :: qs))
        (h (M.icpH M.point) :: (h (M.icpH (M.map.node⁻¹ M.point))
          :: ((M.cpring.drop 3).map fun x => h (M.icpH x))))
        = h (M.icpH M.point) :: (G₀.walkq (G₀.node (h (M.icpH M.point))) q₂'
          ++ rqsWalk G₀ (rq₃ :: qs) (h (M.icpH (M.map.node⁻¹ M.point))
            :: ((M.cpring.drop 3).map fun x => h (M.icpH x)))) :=
      rqsWalk_cons_kernel G₀ _ _ _ _ rfl
    have hstep1 : rqsWalk G₀ (rqsH rq₁ rq₃ qs q₁' q₂')
        (h (M.icpH (M.map.node M.point)) :: h (M.icpH M.point)
          :: h (M.icpH (M.map.node⁻¹ M.point))
            :: ((M.cpring.drop 3).map fun x => h (M.icpH x)))
        = (if rq₁.isKernel = true then [h (M.icpH (M.map.node M.point))] else [])
          ++ (G₀.walkq (G₀.node (h (M.icpH (M.map.node M.point)))) q₁'
            ++ rqsWalk G₀ (RingQuestion.mk true 1 q₂'
                :: (RingQuestion.mk rq₃.isKernel (rq₃.outerArity + 1) rq₃.question :: qs))
              (h (M.icpH M.point) :: (h (M.icpH (M.map.node⁻¹ M.point))
                :: ((M.cpring.drop 3).map fun x => h (M.icpH x))))) := rfl
    rw [hmap1, hstep1, hstep]
  have hK1 : ∀ u, G₀.Fband
        (if rq₁.isKernel = true then [h (M.icpH (M.map.node M.point))] else []) u
      ↔ G₀.Fband (if rq₁.isKernel = true then [h (M.ecpH.map.node .X)] else []) u := by
    intro u
    split_ifs with hk1
    · rw [fband_singleton, fband_singleton]
      exact ⟨fun hc => hc.trans hfaceH.symm, fun hc => hc.trans hfaceH⟩
    · exact Iff.rfl
  have hbandW : ∀ u, G₀.Fband
        (rqsWalk G₀ (rqsH rq₁ rq₃ qs q₁' q₂') (M.cpring.map fun x => h (M.icpH x))) u
      ↔ G₀.Fband (h (M.icpH M.point)
          :: rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpH.cpring.map h)) u := by
    intro u
    have hk2band : G₀.Fband (if rq₂.isKernel = true then [h (.X : M.ecpH.Dart)] else []) u
        ↔ (rq₂.isKernel = true ∧ G₀.CFace u (h (.X : M.ecpH.Dart))) := by
      split_ifs with hk2
      · rw [fband_singleton]
        exact ⟨fun hc => ⟨hk2, hc⟩, fun hc => hc.2⟩
      · exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc.1 hk2⟩
    rw [hWold, hWnew]
    constructor
    · intro hc
      rcases Hypermap.fband_append.mp hc with hc | hc
      · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr
          (Or.inl ((hK1 u).mp hc))))
      rcases Hypermap.fband_append.mp hc with hc | hc
      · rcases (hband u).mp (Or.inl hc) with h1 | h1 | h1
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_append.mpr (Or.inl h1)))))
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr
              (Or.inl (hk2band.mpr h1))))))))
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
              (Hypermap.fband_append.mpr (Or.inl h1)))))))))
      rcases Hypermap.fband_cons.mp hc with hc | hc
      · exact Hypermap.fband_cons.mpr (Or.inl hc)
      rcases Hypermap.fband_append.mp hc with hc | hc
      · rcases (hband u).mp (Or.inr hc) with h1 | h1 | h1
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_append.mpr (Or.inl h1)))))
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr
              (Or.inl (hk2band.mpr h1))))))))
        · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
              (Hypermap.fband_append.mpr (Or.inl h1)))))))))
      · exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
          (Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_append.mpr (Or.inr hc)))))))))
    · intro hc
      rcases Hypermap.fband_cons.mp hc with hc | hc
      · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
          (Hypermap.fband_cons.mpr (Or.inl hc)))))
      rcases Hypermap.fband_append.mp hc with hc | hc
      · exact Hypermap.fband_append.mpr (Or.inl ((hK1 u).mpr hc))
      rcases Hypermap.fband_append.mp hc with hc | hc
      · rcases (hband u).mpr (Or.inl hc) with h1 | h1
        · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inl h1)))
        · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inl h1)))))))
      rcases Hypermap.fband_append.mp hc with hc | hc
      · rcases (hband u).mpr (Or.inr (Or.inl (hk2band.mp hc))) with h1 | h1
        · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inl h1)))
        · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inl h1)))))))
      rcases Hypermap.fband_append.mp hc with hc | hc
      · rcases (hband u).mpr (Or.inr (Or.inr hc)) with h1 | h1
        · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inl h1)))
        · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
            (Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inl h1)))))))
      · exact Hypermap.fband_append.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr
          (Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_append.mpr (Or.inr hc)))))))
  have hlenW : (rqsWalk G₀ (rqsH rq₁ rq₃ qs q₁' q₂')
        (M.cpring.map fun x => h (M.icpH x))).length
      = (rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpH.cpring.map h)).length + 1 := by
    rw [hWold, hWnew]
    simp only [List.length_append, List.length_cons, Hypermap.length_walkq]
    have h1 : (if rq₁.isKernel = true then [h (M.icpH (M.map.node M.point))] else []).length
        = (if rq₁.isKernel = true then [h (M.ecpH.map.node .X)] else []).length := by
      split_ifs <;> rfl
    have h2 : (if rq₂.isKernel = true then [h (.X : M.ecpH.Dart)] else []).length
        = (if rq₂.isKernel = true then 1 else 0) := by
      split_ifs <;> rfl
    rw [h1, h2]
    omega
  have hbandFull : ∀ u, G₀.Fband
        (rqsWalk G₀ (rqsH rq₁ rq₃ qs q₁' q₂')
          (M.cpring.map fun x => h (M.icpH x)) ++ r₀) u
      ↔ G₀.Fband (h (M.icpH M.point)
          :: (rqsWalk G₀ (rq₁ :: rq₂ :: rq₃ :: qs) (M.ecpH.cpring.map h) ++ r₀)) u := by
    intro u
    rw [Hypermap.fband_append, hbandW u, Hypermap.fband_cons, Hypermap.fband_cons,
      Hypermap.fband_append]
    tauto
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr]
    exact ⟨hA1, hq1', hA2', hq2', hA3, hqu3, hfit1⟩
  · intro u hu hnr hnb
    by_cases hcu : G₀.CFace u (h (.X : M.ecpH.Dart))
    · cases hk2 : rq₂.isKernel
      · have hbad : ¬ BadRingArity (rq₂.outerArity + 1) := not_badRingArity_of_cfquizH hk2 hne
        refine goodRingArity_of_not_badRingArity G₀ u ?_
        have harity : G₀.arity u = rq₂.outerArity + 3 := by
          rw [Hypermap.arity_cface _ hcu, hA2]
        rw [harity]
        simpa using hbad
      · exfalso
        obtain ⟨-, -, hdisj⟩ := Hypermap.simple_append.mp hq.simple
        refine hdisj (h (.X : M.ecpH.Dart)) ?_ ⟨u, hu, hcu.symm⟩
        rw [hWold]
        refine List.mem_append_right _ (List.mem_append_right _ ?_)
        refine List.mem_append_left _ ?_
        rw [ite_eq_left hk2]
        exact List.mem_cons_self
    · have hnbH : ¬ G₀.Fband (M.ecpH.cpring.map h) u := by
        rw [hmapH]
        intro hc
        rcases Hypermap.fband_cons.mp hc with hc1 | hc
        · exact hnb (by rw [hmap1]; exact Hypermap.fband_cons.mpr (Or.inl (hc1.trans hfaceH)))
        rcases Hypermap.fband_cons.mp hc with hc1 | hc
        · exact hcu hc1
        · refine hnb ?_
          rw [hmap1]
          exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inr hc)))
      have hnv2 : ¬ G₀.CFace u (h (M.icpH M.point)) := by
        intro hc
        refine hnb ?_
        rw [hmap1]
        exact Hypermap.fband_cons.mpr (Or.inr (Hypermap.fband_cons.mpr (Or.inl hc)))
      have hnrH : u ∉ Set.range h := by
        rcases (hP u).mpr (Or.inl hnr) with hc | hc | hc
        · exact absurd hc hnv2
        · exact hc
        · exact absurd hc hnbH
      exact hq.ringArity u hu hnrH hnbH
  · refine (Hypermap.simple_iff_of_fband_eq hbandFull ?_).mpr
      (Hypermap.simple_cons.mpr ⟨hv2band, hq.simple⟩)
    rw [List.length_append, List.length_cons, List.length_append, hlenW]
    omega
  · intro u
    rw [hbandFull u, Hypermap.fband_cons, Hypermap.fband_append, ← Hypermap.fband_append,
      hq.cover u, hP u]


/-! ### Putting the steps together

The invariant is set up for the full configuration map, carried through the
program one step at a time, and read off as a valid quiz when the program is
exhausted. -/

/-- The initial ring questions visit no dart. -/
private theorem rqsWalk_replicate {D₀ : Type*} (G₀ : Hypermap D₀) : ∀ (n : ℕ) (p : List D₀),
    rqsWalk G₀ (List.replicate n initRingQuestion) p = [] := by
  intro n
  induction n with
  | zero => intro p; rw [List.replicate_zero, rqsWalk_nil_left]
  | succ n ih =>
    intro p
    cases p with
    | nil => rw [rqsWalk_nil_right]
    | cons u p =>
      rw [List.replicate_succ, rqsWalk_cons, ih p]
      rfl

/-- The initial ring questions fit the ring of the full map. -/
private theorem rqsFit_replicate {D : Type*} (G : Hypermap D) : ∀ (p : List D),
    rqsFit G G id (List.replicate p.length initRingQuestion) p := by
  intro p
  induction p with
  | nil => exact trivial
  | cons x p ih =>
    rw [List.length_cons, List.replicate_succ]
    exact ⟨(Nat.zero_add _).symm, rfl, ih⟩

/-- **The compiler is correct**: if the ring questions `qs` are proper for the
part of the program already run and the compiled quiz is a right quiz, then the
perimeter of the full map has good ring arities and the quiz is valid for it. -/
theorem cfquizRec_valid : ∀ (cp2 : CProg), (cp2 = [] ∨ ConfigProg cp2) →
    ∀ (cp1 : CProg), CubicProg cp1 → ∀ (qs : List RingQuestion),
      RqsProper (cpmap (cp1.reverseAux cp2)).map (cpmap cp2).map (injcp cp1 cp2)
        (cpmap (cp1.reverseAux cp2)).cpring (cpmap cp2).cpring qs →
      (cfquizRec cp2 qs).IsQuizR →
      (∀ u ∈ (cpmap (cp1.reverseAux cp2)).cpring,
          (cpmap (cp1.reverseAux cp2)).map.GoodRingArity u) ∧
        ∃ x₀, (cpmap (cp1.reverseAux cp2)).map.ValidQuiz
          (cpmap (cp1.reverseAux cp2)).cpring x₀ (cfquizRec cp2 qs) := by
  intro cp2
  induction cp2 with
  | nil =>
    intro _ cp1 hcp1 qs hq hR
    exact cfquizRec_nil_valid _ _ (injcp cp1 []) (edge_injcp cp1 hcp1 []) qs hq hR
  | cons s cp2 ih =>
    intro hcfg cp1 hcp1 qs hq hR
    have hcfg' : ConfigProg (s :: cp2) := by
      rcases hcfg with hc | hc
      · exact absurd hc (by simp)
      · exact hc
    have hs : s.IsConfig := hcfg'.1 s List.mem_cons_self
    have h3 : 3 ≤ qs.length := by
      by_contra hlt
      rw [cfquizRec_cons_of_length_lt (by omega)] at hR
      exact not_isQuizR_noquiz hR
    obtain ⟨rq₁, rq₂, rq₃, qs', rfl⟩ : ∃ a b c t, qs = a :: b :: c :: t := by
      match qs, h3 with
      | a :: b :: c :: t, _ => exact ⟨a, b, c, t, rfl⟩
    have hrest : cp2 = [] ∨ ConfigProg cp2 := by
      by_cases hnil : cp2 = []
      · exact Or.inl hnil
      · exact Or.inr (hcfg'.of_cons hnil)
    have hcub2 : CubicProg cp2 := by
      rcases hrest with rfl | hc
      · exact cubicProg_nil
      · exact hc.cubicProg
    have hp2 : (cpmap cp2).Proper := cpmap_proper hcub2
    have hUr2 : (cpmap cp2).map.Simple (cpmap cp2).cpring := by
      rcases hrest with rfl | hcfg2
      · exact (Hypermap.simple_append.mp simple_cpmap0).1
      · exact (Hypermap.simple_append.mp (cpmap_simple hcfg2)).1
    have hcp1' : ∀ t : CpStep, t.IsCubic → CubicProg (t :: cp1) := by
      intro t ht u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht
      · exact hcp1 u hu
    cases s with
    | R n =>
      rw [cfquizRec_R] at hR
      have hring : (cpmap (CpStep.R n :: cp2)).cpring = (cpmap cp2).cpring.rotate n :=
        Hypermap.cpring_ecpR (G := (cpmap cp2).map) (x₀ := (cpmap cp2).point) n
      have hqR : RqsProper (cpmap (cp1.reverseAux (CpStep.R n :: cp2))).map (cpmap cp2).map
          (injcp cp1 (CpStep.R n :: cp2))
          (cpmap (cp1.reverseAux (CpStep.R n :: cp2))).cpring
          ((cpmap cp2).cpring.rotate n) (rq₁ :: rq₂ :: rq₃ :: qs') := by
        rw [← hring]
        exact hq
      exact ih hrest (CpStep.R n :: cp1) (hcp1' _ trivial) _
        (rqsProper_R _ _ n cp2 (injcp cp1 (CpStep.R n :: cp2)) _ hqR) hR
    | Y =>
      rw [cfquizRec_Y] at hR
      have hne : cfquizY rq₁ rq₂ (rqsY rq₁ rq₃ qs') ≠ [] := by
        intro he
        rw [he, cfquizRec_nil_questions] at hR
        exact not_isQuizR_noquiz hR
      have hprop := rqsProper_Y (cpmap (cp1.reverseAux (CpStep.Y :: cp2))).map
        (cpmap (cp1.reverseAux (CpStep.Y :: cp2))).cpring (cpmap cp2) hp2 hUr2
        (injcp cp1 (CpStep.Y :: cp2)) (edge_injcp cp1 hcp1 (CpStep.Y :: cp2))
        (fun x hx => node_injcp cp1 hcp1 (CpStep.Y :: cp2) x hx)
        (cface_injcp cp1 hcp1 (CpStep.Y :: cp2)) rq₁ rq₂ rq₃ qs' hq hne
      exact ih hrest (CpStep.Y :: cp1) (hcp1' _ trivial) _ hprop hR
    | H =>
      rw [cfquizRec_H] at hR
      have hne : cfquizH rq₁ rq₂ (rqsH rq₁ rq₃ qs') ≠ [] := by
        intro he
        rw [he, cfquizRec_nil_questions] at hR
        exact not_isQuizR_noquiz hR
      have hnil2 : cp2 ≠ [] := by
        rintro rfl
        have h2 := hcfg'.2
        simp at h2
      have hcfg2 : ConfigProg cp2 := hcfg'.of_cons hnil2
      have hlong : (cpmap cp2).Long := cfmap_long hcfg2
      have hprop := rqsProper_H (cpmap (cp1.reverseAux (CpStep.H :: cp2))).map
        (cpmap (cp1.reverseAux (CpStep.H :: cp2))).cpring (cpmap cp2) hlong hUr2
        (injcp cp1 (CpStep.H :: cp2)) (injcp_injective cp1 (CpStep.H :: cp2))
        (edge_injcp cp1 hcp1 (CpStep.H :: cp2))
        (fun x hx => node_injcp cp1 hcp1 (CpStep.H :: cp2) x hx)
        (cface_injcp cp1 hcp1 (CpStep.H :: cp2)) rq₁ rq₂ rq₃ qs' hq hne
      exact ih hrest (CpStep.H :: cp1) (hcp1' _ trivial) _ hprop hR
    | R' => exact hs.elim
    | U => exact hs.elim
    | K => exact hs.elim
    | A => exact hs.elim

/-- **The quiz of a configuration is valid**: its perimeter has good ring
arities, and the quiz tests for the configuration at one of its darts. -/
theorem cfquizP {cf : Config} (hR : (cfquiz cf).IsQuizR) :
    (∀ u ∈ (cfmap cf).cpring, (cfmap cf).map.GoodRingArity u) ∧
      ∃ x₀, (cfmap cf).map.ValidQuiz (cfmap cf).cpring x₀ (cfquiz cf) := by
  have hcp : ConfigProg cf.prog := ConfigProg.of_cfquiz hR
  have heq := cfquiz_eq_cfquizRec (cpradius2_of_cfquiz hR)
  rw [heq] at hR ⊢
  have hUr : (cpmap cf.prog).map.Simple (cpmap cf.prog).cpring :=
    (Hypermap.simple_append.mp (cpmap_simple hcp)).1
  have hqs : List.replicate (cprsize cf.prog) initRingQuestion
      = List.replicate ((cpmap cf.prog).cpring).length initRingQuestion := by
    rw [size_ring_cpmap]
  have hmapid : (cpmap cf.prog).cpring.map (injcp [] cf.prog) = (cpmap cf.prog).cpring :=
    List.map_id _
  have hwalk : rqsWalk (cpmap (List.reverseAux [] cf.prog)).map
      (List.replicate (cprsize cf.prog) initRingQuestion)
      ((cpmap cf.prog).cpring.map (injcp [] cf.prog)) = [] :=
    rqsWalk_replicate _ _ _
  have hrange : ∀ u : (cpmap cf.prog).Dart, u ∈ Set.range (injcp [] cf.prog) := fun u => ⟨u, rfl⟩
  have hprop : RqsProper (cpmap (List.reverseAux [] cf.prog)).map (cpmap cf.prog).map
      (injcp [] cf.prog) (cpmap (List.reverseAux [] cf.prog)).cpring (cpmap cf.prog).cpring
      (List.replicate (cprsize cf.prog) initRingQuestion) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hqs]
      exact rqsFit_replicate _ _
    · intro u _ hnr _
      exact absurd (hrange u) hnr
    · rw [hwalk, List.nil_append]
      exact hUr
    · intro u
      rw [hwalk, List.nil_append, hmapid]
      exact ⟨fun hc => Or.inr hc, fun hc => hc.elim (fun hnr => absurd (hrange u) hnr) id⟩
  exact cfquizRec_valid cf.prog (Or.inr hcp) [] cubicProg_nil _ hprop hR

/-- **The quiz of a configuration is a valid quiz for its ring.** -/
theorem valid_cfquiz {cf : Config} (hR : (cfquiz cf).IsQuizR) :
    ∃ x₀, (cfmap cf).map.ValidQuiz (cfring cf) x₀ (cfquiz cf) := by
  obtain ⟨-, x₀, h1, h2, h3, h4⟩ := cfquizP hR
  exact ⟨x₀, h1, h2, h3, fun y => (h4 y).trans (not_congr Hypermap.fband_reverse).symm⟩

/-- **The map of a configuration is embeddable**: it satisfies all the
geometrical requirements of the embedding development. -/
theorem embeddable_cfquiz {cf : Config} (hR : (cfquiz cf).IsQuizR) :
    (cfmap cf).map.Embeddable (cfring cf) := by
  have hcp : ConfigProg cf.prog := ConfigProg.of_cfquiz hR
  have hcub : CubicProg cf.prog := hcp.cubicProg
  have hUr : (cpmap cf.prog).map.Simple (cpmap cf.prog).cpring :=
    (Hypermap.simple_append.mp (cpmap_simple hcp)).1
  have hqc : (cpmap cf.prog).map.CubicOn {x | x ∉ (cpmap cf.prog).cpring} := cpmap_cubic hcub
  refine ⟨⟨⟨⟨⟨cpmap_plain hcub, ⟨?_, ?_⟩⟩,
    Hypermap.isCyclicChain_reverse_cpring, ?_⟩, cpmap_connected hcub⟩,
    Hypermap.simple_reverse.mpr hUr, cpmap_planar hcub, cpmap_bridgeless hcub⟩,
    ?_, cpradius2P hR⟩
  · exact fun x hx => hqc.node_node_node x fun hc => hx (List.mem_reverse.mpr hc)
  · exact fun x hx => hqc.node_ne x fun hc => hx (List.mem_reverse.mpr hc)
  · exact List.nodup_reverse.mpr (nodup_cpring_pointed _)
  · exact fun x hx => (cfquizP hR).1 x (List.mem_reverse.mp hx)

/-! ### A sanity check on the compiler

The reference checks dynamically, for each of the 633 configuration programs,
that the compiled quiz is a right quiz; `ConfigProg.of_cfquiz` is what turns
such a check into a statement about the program.  The check has been run here
for all 633 programs of `FourColor.Configurations`; three of them are kept as
regression tests, the shortest, the next one, and the longest. -/

/-- The quiz compiled for configuration 1 is a right quiz. -/
example : (cfquiz ⟨true, [13],
    [.H, .R 3, .H, .R 5, .H, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y]⟩).IsQuizR :=
  ⟨trivial, trivial⟩

/-- The quiz compiled for configuration 2 is a right quiz. -/
example : (cfquiz ⟨true, [6],
    [.H, .R 2, .H, .R 6, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y]⟩).IsQuizR :=
  ⟨trivial, trivial⟩

/-- The quiz compiled for configuration 633 is a right quiz. -/
example : (cfquiz ⟨true, [6],
    [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 9, .H, .R 9,
      .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .Y, .Y, .Y]⟩).IsQuizR :=
  ⟨trivial, trivial⟩

end FourColor

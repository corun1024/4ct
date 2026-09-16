import FourColor.Color

/-!
# Chromograms

A chromogram is a word recording a congruence class of regions under Kempe
inversions for one edge colour and colour permutation.  The topological content
of such a class is a set of non-crossing chords linking perimeter edges,
together with the parity of each chord; the word representing it is a Dyck word
augmented with *spaces* (perimeter edges not linked, because coloured with the
inversion colour) and parities on the closing brackets.

The reference introduces a bespoke `bit_stack` type as an "algorithmic"
stand-in for a list of bits; in Lean `List Bool` already is that inductive type,
so `matchpg` simply takes a `List Bool` and the conversion layer disappears.

## Main definitions

* `GramSymbol`, `Chromogram` — the alphabet and the words.
* `balanced d b w` — `w` is balanced with `d` open chords and parity `b`.
* `matchg lb et w` — the trace `et` matches `w` with open chords `lb`.
* `matchpg`, `cgram` — the partial-chromogram forms used by the reducibility check.
* `KempeClosed`, `KempeCoclosure` — closure of a set of traces under Kempe flips.

## References

Gonthier's `theories/proof/chromogram.v`.
-/

namespace List

/-- The parity of the length of a list, as a boolean. -/
def parityLen {α : Type*} : List α → Bool
  | [] => false
  | _ :: l => !parityLen l

/-- The exclusive-or of a list of bits. -/
def xorAll : List Bool → Bool
  | [] => false
  | b :: l => xor b (xorAll l)

@[simp] theorem parityLen_nil {α : Type*} : ([] : List α).parityLen = false := rfl

@[simp] theorem parityLen_cons {α : Type*} (a : α) (l : List α) :
    (a :: l).parityLen = !l.parityLen := rfl

@[simp] theorem xorAll_nil : ([] : List Bool).xorAll = false := rfl

@[simp] theorem xorAll_cons (b : Bool) (l : List Bool) :
    (b :: l).xorAll = xor b l.xorAll := rfl

end List

namespace FourColor

open Color

/-- A chromogram symbol. -/
inductive GramSymbol
  /-- Chord start: the edge has colour `c2` or `c3`. -/
  | push
  /-- No chord: the edge has colour `c1`. -/
  | skip
  /-- Odd chord end: the ending edge has the same colour as the start. -/
  | pop0
  /-- Even chord end: start and end have different colours. -/
  | pop1
  deriving DecidableEq, Repr, Inhabited

/-- A chromogram: a word of chromogram symbols. -/
abbrev Chromogram := List GramSymbol


/-- `balanced d b w` says the chromogram `w` is balanced in a context with `d`
open chords, and has parity `b`. -/
def balanced : ℕ → Bool → Chromogram → Bool
  | d, b₀, [] => (d == 0) && !b₀
  | d, b₀, .push :: w => balanced (d + 1) b₀ w
  | d, b₀, .skip :: w => balanced d (!b₀) w
  | 0, _, .pop0 :: _ => false
  | d + 1, b₀, .pop0 :: w => balanced d b₀ w
  | 0, _, .pop1 :: _ => false
  | d + 1, b₀, .pop1 :: w => balanced d (!b₀) w

@[simp] theorem balanced_nil (d : ℕ) (b : Bool) : balanced d b [] = ((d == 0) && !b) := rfl

@[simp] theorem balanced_push (d : ℕ) (b : Bool) (w : Chromogram) :
    balanced d b (.push :: w) = balanced (d + 1) b w := rfl

@[simp] theorem balanced_skip (d : ℕ) (b : Bool) (w : Chromogram) :
    balanced d b (.skip :: w) = balanced d (!b) w := rfl

@[simp] theorem balanced_pop0_zero (b : Bool) (w : Chromogram) :
    balanced 0 b (.pop0 :: w) = false := rfl

@[simp] theorem balanced_pop0_succ (d : ℕ) (b : Bool) (w : Chromogram) :
    balanced (d + 1) b (.pop0 :: w) = balanced d b w := rfl

@[simp] theorem balanced_pop1_zero (b : Bool) (w : Chromogram) :
    balanced 0 b (.pop1 :: w) = false := rfl

@[simp] theorem balanced_pop1_succ (d : ℕ) (b : Bool) (w : Chromogram) :
    balanced (d + 1) b (.pop1 :: w) = balanced d (!b) w := rfl

/-- One matching step: consume the colour `e` against the symbol `s` in a
context of open chords `bs`, returning the new context, or `none` if the colour
and symbol are incompatible.  `matchg` and `matchpg` differ only in their base
case, so they share this step. -/
def matchStep : Color → GramSymbol → List Bool → Option (List Bool)
  | .c1, .skip, bs => some bs
  | .c2, .push, bs => some (false :: bs)
  | .c2, .pop0, false :: bs => some bs
  | .c2, .pop1, true :: bs => some bs
  | .c3, .push, bs => some (true :: bs)
  | .c3, .pop0, true :: bs => some bs
  | .c3, .pop1, false :: bs => some bs
  | _, _, _ => none

/-- `matchg lb et w` says the edge-colouring trace `et` matches the chromogram
`w` in a context with `lb.length` open chords whose edge-colour parities are
`lb` reversed. -/
def matchg : List Bool → List Color → Chromogram → Bool
  | lb, [], [] => lb.isEmpty
  | lb, e :: et, s :: w => (matchStep e s lb).elim false fun lb' => matchg lb' et w
  | _, _, _ => false

/-- `matchpg` is `matchg` for *partial* chromograms: the final symbol of the
word and the final colour of the trace are both left implicit, so no condition
is imposed on the remaining open chords. -/
def matchpg : List Bool → List Color → Chromogram → Bool
  | _, [], [] => true
  | bs, e :: et, s :: w => (matchStep e s bs).elim false fun bs' => matchpg bs' et w
  | _, _, _ => false

@[simp] theorem matchg_nil_nil (lb : List Bool) : matchg lb [] [] = lb.isEmpty := rfl

@[simp] theorem matchg_cons (lb : List Bool) (e : Color) (et : List Color)
    (s : GramSymbol) (w : Chromogram) :
    matchg lb (e :: et) (s :: w)
      = (matchStep e s lb).elim false fun lb' => matchg lb' et w := rfl

@[simp] theorem matchg_cons_nil (lb : List Bool) (e : Color) (et : List Color) :
    matchg lb (e :: et) [] = false := rfl

@[simp] theorem matchg_nil_cons (lb : List Bool) (s : GramSymbol) (w : Chromogram) :
    matchg lb [] (s :: w) = false := rfl

@[simp] theorem matchpg_nil (bs : List Bool) : matchpg bs [] [] = true := rfl

@[simp] theorem matchpg_cons (bs : List Bool) (e : Color) (et : List Color)
    (s : GramSymbol) (w : Chromogram) :
    matchpg bs (e :: et) (s :: w)
      = (matchStep e s bs).elim false fun bs' => matchpg bs' et w := rfl

@[simp] theorem matchpg_cons_nil (bs : List Bool) (e : Color) (et : List Color) :
    matchpg bs (e :: et) [] = false := rfl

@[simp] theorem matchpg_nil_cons (bs : List Bool) (s : GramSymbol) (w : Chromogram) :
    matchpg bs [] (s :: w) = false := rfl

/-- `cgram d b w` restores the last symbol of a partial chromogram `w`, in a
context with `d` open chords and parity `b`. -/
def cgram : ℕ → Bool → Chromogram → Chromogram
  | d, b₀, [] => [if d = 0 then .skip else if b₀ then .pop1 else .pop0]
  | d, b₀, .push :: w => .push :: cgram (d + 1) b₀ w
  | d, b₀, .skip :: w => .skip :: cgram d (!b₀) w
  | d, b₀, .pop0 :: w => .pop0 :: cgram (d - 1) b₀ w
  | d, b₀, .pop1 :: w => .pop1 :: cgram (d - 1) (!b₀) w

/-- A set of traces is Kempe-closed when it is stable under colour permutations
and under Kempe flips: each of its traces matches a chromogram all of whose
matching traces are again in the set. -/
def KempeClosed (P : List Color → Prop) : Prop :=
  ∀ et, P et → (∀ g : EdgePerm, P (et.map g)) ∧
    ∃ w, matchg [] et w ∧ ∀ et', matchg [] et' w → P et'

/-- `P` meets every Kempe-closed predicate holding for `et`. -/
def KempeCoclosure (P : List Color → Prop) (et : List Color) : Prop :=
  ∀ P', KempeClosed P' → P' et → ∃ et', P et' ∧ P' et'

/-- **Co-closure from a well-founded certificate.**

A Kempe-closed predicate chooses, for each of its traces, *some* chromogram all
of whose matches it also holds; so to place a trace in the co-closure one has to
answer *every* chromogram matching it.  A certificate does that by well-founded
descent: `S` is a set of traces ranked by `rank`, and each trace of `S` answers
each of its chromograms with a matching trace that is either already in `P` or,
after some colour permutation, of strictly smaller rank.  The permutation is
inside the descent because a Kempe-closed predicate is closed under colour
permutations, so an answer may be justified only up to one — which is exactly
what the closure loop's symmetrisation of its removals produces.

This is the fixpoint the Kempe closure loop computes, presented as something to
*check* rather than to *compute*: the condition is local to one trace, so it can
be verified a trace at a time, independently, and — for a large configuration —
split across as many declarations as the kernel's memory requires. -/
theorem kempeCoclosure_of_rank {P S : List Color → Prop} (rank : List Color → ℕ)
    (hcert : ∀ et, S et → ∀ w, matchg [] et w →
      ∃ et', matchg [] et' w ∧
        (P et' ∨ ∃ g : EdgePerm, S (et'.map g) ∧ rank (et'.map g) < rank et))
    {et : List Color} (hS : S et) : KempeCoclosure P et := by
  -- Strong induction on the rank, with the trace and the closed predicate free.
  have key : ∀ n et, rank et = n → S et → KempeCoclosure P et := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro et hn hSet P1 hP1 hP1et
      -- the closed predicate supplies one chromogram matching `et`
      obtain ⟨hperm, w, hmw, hwP1⟩ := hP1 et hP1et
      -- and the certificate answers it
      obtain ⟨et', hmw', hcase⟩ := hcert et hSet w hmw
      have hP1et' : P1 et' := hwP1 et' hmw'
      rcases hcase with hPet' | ⟨g, hSg, hlt⟩
      · exact ⟨et', hPet', hP1et'⟩
      · -- the answer is justified only after a colour permutation, which the
        -- closed predicate also holds
        exact ih (rank (et'.map g)) (hn ▸ hlt) _ rfl hSg P1 hP1 ((hP1 et' hP1et').1 g)
  exact key (rank et) et rfl hS

end FourColor

namespace FourColor

open Color

/-! ### Basic properties of matching -/

theorem matchStep_ne_zero {e : Color} {s : GramSymbol} {bs bs' : List Bool}
    (h : matchStep e s bs = some bs') : e ≠ 0 := by
  cases e <;> simp_all [matchStep]

theorem matchg_length : ∀ (et : List Color) (lb : List Bool) (w : Chromogram),
    matchg lb et w → w.length = et.length := by
  intro et
  induction et with
  | nil =>
    intro lb w h
    cases w with
    | nil => rfl
    | cons s w => simp [matchg] at h
  | cons e et ih =>
    intro lb w h
    cases w with
    | nil => simp at h
    | cons s w =>
      rw [matchg_cons] at h
      cases hs : matchStep e s lb with
      | none => rw [hs] at h; simp at h
      | some lb' =>
        rw [hs] at h
        simp only [Option.elim] at h
        simp [ih lb' w h]

theorem matchpg_length : ∀ (et : List Color) (bs : List Bool) (w : Chromogram),
    matchpg bs et w → w.length = et.length := by
  intro et
  induction et with
  | nil =>
    intro bs w h
    cases w with
    | nil => rfl
    | cons s w => simp [matchpg] at h
  | cons e et ih =>
    intro bs w h
    cases w with
    | nil => simp at h
    | cons s w =>
      rw [matchpg_cons] at h
      cases hs : matchStep e s bs with
      | none => rw [hs] at h; simp at h
      | some bs' =>
        rw [hs] at h
        simp only [Option.elim] at h
        simp [ih bs' w h]

/-- A matched trace never contains the failure colour. -/
theorem matchg_notMem_zero : ∀ (et : List Color) (lb : List Bool) (w : Chromogram),
    matchg lb et w → (0 : Color) ∉ et := by
  intro et
  induction et with
  | nil => intro _ _ _; simp
  | cons e et ih =>
    intro lb w h
    cases w with
    | nil => simp at h
    | cons s w =>
      rw [matchg_cons] at h
      cases hs : matchStep e s lb with
      | none => rw [hs] at h; simp at h
      | some lb' =>
        rw [hs] at h
        simp only [Option.elim] at h
        simp only [List.mem_cons, not_or]
        exact ⟨fun he => matchStep_ne_zero hs he.symm, ih lb' w h⟩

/-- A chromogram determines the context it is balanced in. -/
theorem balanced_inj : ∀ (w : Chromogram) (n₁ n₂ : ℕ) (b₁ b₂ : Bool),
    balanced n₁ b₁ w → balanced n₂ b₂ w → n₁ = n₂ ∧ b₁ = b₂ := by
  intro w
  induction w with
  | nil =>
    intro n₁ n₂ b₁ b₂ h₁ h₂
    simp only [balanced_nil, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h₁ h₂
    exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
  | cons s w ih =>
    intro n₁ n₂ b₁ b₂ h₁ h₂
    cases s with
    | push =>
      simp only [balanced_push] at h₁ h₂
      obtain ⟨hn, hb⟩ := ih _ _ _ _ h₁ h₂
      exact ⟨by omega, hb⟩
    | skip =>
      simp only [balanced_skip] at h₁ h₂
      obtain ⟨hn, hb⟩ := ih _ _ _ _ h₁ h₂
      exact ⟨hn, by simpa using hb⟩
    | pop0 =>
      match n₁, n₂ with
      | 0, _ => simp at h₁
      | _ + 1, 0 => simp at h₂
      | _ + 1, _ + 1 =>
        simp only [balanced_pop0_succ] at h₁ h₂
        obtain ⟨hn, hb⟩ := ih _ _ _ _ h₁ h₂
        exact ⟨by omega, hb⟩
    | pop1 =>
      match n₁, n₂ with
      | 0, _ => simp at h₁
      | _ + 1, 0 => simp at h₂
      | _ + 1, _ + 1 =>
        simp only [balanced_pop1_succ] at h₁ h₂
        obtain ⟨hn, hb⟩ := ih _ _ _ _ h₁ h₂
        exact ⟨by omega, by simpa using hb⟩

/-! ### Matching implies balance -/

/-- The generalised form of `matchg_balanced`: a match in a context of open
chords `lb` forces the parity of the trace sum and the balance of the word. -/
theorem matchg_balanced_gen : ∀ (et : List Color) (lb : List Bool) (w : Chromogram),
    matchg lb et w →
      et.sum.hi = lb.parityLen ∧ balanced lb.length (xor lb.xorAll et.sum.lo) w := by
  intro et
  induction et with
  | nil =>
    intro lb w h
    cases w with
    | cons s w => simp [matchg] at h
    | nil =>
      simp only [matchg_nil_nil, List.isEmpty_iff] at h
      subst h
      simp [balanced]
  | cons e et ih =>
    intro lb w h
    cases w with
    | nil => simp at h
    | cons s w =>
      cases e <;> cases s <;> rcases lb with _ | ⟨b, lb⟩ <;> (try cases b) <;>
        simp only [matchg_cons, matchStep, Option.elim] at h <;>
        first
          | simp at h
          | (obtain ⟨ih1, ih2⟩ := ih _ w h
             simp_all [balanced, List.sum_cons, List.parityLen, List.xorAll])

/-- A trace matching a chromogram in the empty context has even high-bit sum,
and the chromogram is balanced with the parity of the trace's low bit. -/
theorem matchg_balanced {et : List Color} {w : Chromogram} (h : matchg [] et w) :
    et.sum.hi = false ∧ balanced 0 et.sum.lo w := by
  obtain ⟨h1, h2⟩ := matchg_balanced_gen et [] w h
  exact ⟨h1, by simpa using h2⟩

/-- A trace matching a balanced chromogram sums to zero. -/
theorem sum_eq_zero_of_matchg {et : List Color} {w : Chromogram}
    (hw : balanced 0 false w) (h : matchg [] et w) : et.sum = 0 := by
  obtain ⟨h1, h2⟩ := matchg_balanced h
  have h3 := (balanced_inj w 0 0 et.sum.lo false h2 hw).2
  cases hsum : et.sum <;> simp_all

/-! ### Invariance under the colour flip -/

/-- Swapping `c2` and `c3` in a colour is absorbed by flipping every open-chord
parity. -/
theorem matchStep_e132 (e : Color) (s : GramSymbol) (bs : List Bool) :
    matchStep (EdgePerm.e132 e) s (bs.map not)
      = (matchStep e s bs).map (List.map not) := by
  cases e <;> cases s <;> rcases bs with _ | ⟨b, bs⟩ <;> (try cases b) <;> rfl

theorem matchg_map_e132 : ∀ (et : List Color) (lb : List Bool) (w : Chromogram),
    matchg (lb.map not) (et.map EdgePerm.e132) w = matchg lb et w := by
  intro et
  induction et with
  | nil => intro lb w; cases w <;> simp
  | cons e et ih =>
    intro lb w
    cases w with
    | nil => simp
    | cons s w =>
      rw [List.map_cons, matchg_cons, matchg_cons, matchStep_e132]
      cases matchStep e s lb with
      | none => rfl
      | some lb' => exact ih lb' w

theorem matchpg_map_e132 : ∀ (et : List Color) (bs : List Bool) (w : Chromogram),
    matchpg (bs.map not) (et.map EdgePerm.e132) w = matchpg bs et w := by
  intro et
  induction et with
  | nil => intro bs w; cases w <;> simp
  | cons e et ih =>
    intro bs w
    cases w with
    | nil => simp
    | cons s w =>
      rw [List.map_cons, matchpg_cons, matchpg_cons, matchStep_e132]
      cases matchStep e s bs with
      | none => rfl
      | some bs' => exact ih bs' w

/-- Matching is invariant under evening out a trace. -/
theorem matchg_evenize (et : List Color) (w : Chromogram) :
    matchg [] (evenize et) w = matchg [] et w := by
  rw [evenize]
  rcases evenPerm_eq_one_or et with h | h <;> rw [h]
  · simp
  · simpa using matchg_map_e132 et [] w

theorem matchpg_evenize (et : List Color) (w : Chromogram) :
    matchpg [] (evenize et) w = matchpg [] et w := by
  rw [evenize]
  rcases evenPerm_eq_one_or et with h | h <;> rw [h]
  · simp
  · simpa using matchpg_map_e132 et [] w

/-! ### Chromogram completion -/

/-- A balanced chromogram is the completion of its own prefix.  This is the
combinatorial content of the reference's `matchg_cgram`. -/
theorem eq_cgram_take_of_balanced : ∀ (w : Chromogram) (s : GramSymbol) (d : ℕ) (b : Bool),
    balanced d b (s :: w) → s :: w = cgram d b ((s :: w).take w.length) := by
  intro w
  induction w with
  | nil =>
    intro s d b h
    cases s with
    | push => simp [balanced] at h
    | skip =>
      match d, b with
      | 0, true => rfl
      | 0, false => simp [balanced] at h
      | _ + 1, _ => simp [balanced] at h
    | pop0 =>
      match d, b with
      | 0, _ => simp [balanced] at h
      | 1, false => rfl
      | 1, true => simp [balanced] at h
      | _ + 2, _ => simp [balanced] at h
    | pop1 =>
      match d, b with
      | 0, _ => simp [balanced] at h
      | 1, true => rfl
      | 1, false => simp [balanced] at h
      | _ + 2, _ => simp [balanced] at h
  | cons s' w ih =>
    intro s d b h
    have htake : (s :: s' :: w).take (s' :: w).length
        = s :: (s' :: w).take w.length := by
      simp [List.take_succ_cons]
    rw [htake]
    cases s with
    | push =>
      rw [balanced] at h
      rw [cgram, ← ih s' (d + 1) b h]
    | skip =>
      rw [balanced] at h
      rw [cgram, ← ih s' d (!b) h]
    | pop0 =>
      match d, h with
      | d + 1, h =>
        rw [balanced] at h
        rw [cgram, Nat.add_sub_cancel, ← ih s' d b h]
    | pop1 =>
      match d, h with
      | d + 1, h =>
        rw [balanced] at h
        rw [cgram, Nat.add_sub_cancel, ← ih s' d (!b) h]

/-- A chromogram matched by a completed trace is itself a completion. -/
theorem matchg_cgram {et : List Color} {cw : Chromogram}
    (h : matchg [] (completeTrace et) cw) :
    cw = cgram 0 false (cw.take (cw.length - 1)) := by
  have hb := (matchg_balanced h).2
  rw [sum_completeTrace] at hb
  simp only [Color.lo_zero] at hb
  cases cw with
  | nil =>
    exfalso
    have : (completeTrace et).length = 0 := by
      simpa using (matchg_length _ _ _ h).symm
    simp [completeTrace] at this
  | cons s w =>
    simpa using eq_cgram_take_of_balanced w s 0 false hb

/-! ### Complete versus partial matching -/

/-- The depth transition of `cgram` at one symbol. -/
def cgramDepth : GramSymbol → ℕ → ℕ
  | .push, d => d + 1
  | .skip, d => d
  | .pop0, d => d - 1
  | .pop1, d => d - 1

/-- The parity transition of `cgram` at one symbol. -/
def cgramBit : GramSymbol → Bool → Bool
  | .push, b => b
  | .skip, b => !b
  | .pop0, b => b
  | .pop1, b => !b

@[simp] theorem cgram_cons (d : ℕ) (b : Bool) (s : GramSymbol) (w : Chromogram) :
    cgram d b (s :: w) = s :: cgram (cgramDepth s d) (cgramBit s b) w := by
  cases s <;> rfl

theorem cgram_ne_nil (d : ℕ) (b : Bool) (w : Chromogram) : cgram d b w ≠ [] := by
  cases w with
  | nil => cases d <;> simp [cgram]
  | cons s w => simp

/-- The colour that closes a trace in a context of open chords `lb` and parity `b`. -/
def closingColor (lb : List Bool) (b : Bool) : Color :=
  Color.ofBits lb.parityLen (xor b lb.xorAll)

@[simp] theorem ofBits_add_c1 (p x : Bool) :
    Color.ofBits p x + Color.c1 = Color.ofBits p (!x) := by cases p <;> cases x <;> rfl

@[simp] theorem ofBits_add_c2 (p x : Bool) :
    Color.ofBits p x + Color.c2 = Color.ofBits (!p) x := by cases p <;> cases x <;> rfl

@[simp] theorem ofBits_add_c3 (p x : Bool) :
    Color.ofBits p x + Color.c3 = Color.ofBits (!p) (!x) := by cases p <;> cases x <;> rfl

/-- A matching step moves the open-chord count exactly as `cgram` moves its depth. -/
theorem matchStep_length {e : Color} {s : GramSymbol} {lb lb' : List Bool}
    (h : matchStep e s lb = some lb') : lb'.length = cgramDepth s lb.length := by
  cases e <;> cases s <;> rcases lb with _ | ⟨c, lb⟩ <;> (try cases c) <;>
    simp only [matchStep, Option.some.injEq] at h <;>
    first
      | (subst h; simp [cgramDepth])
      | simp at h

/-- A matching step moves the closing colour by exactly the colour consumed. -/
theorem closingColor_step {e : Color} {s : GramSymbol} {lb lb' : List Bool} (b : Bool)
    (h : matchStep e s lb = some lb') :
    closingColor lb' (cgramBit s b) = closingColor lb b + e := by
  cases e <;> cases s <;> rcases lb with _ | ⟨c, lb⟩ <;> (try cases c) <;>
    simp only [matchStep, Option.some.injEq] at h <;>
    first
      | (subst h
         simp only [closingColor, cgramBit, List.parityLen, List.xorAll]
         cases b <;> simp [Bool.xor_comm])
      | simp at h

@[simp] theorem matchg_append_nil (lb : List Bool) (et : List Color) (c : Color) :
    matchg lb (et ++ [c]) [] = false := by cases et <;> rfl

theorem matchg_singleton_of_cons_cons (lb : List Bool) (c : Color)
    (s s' : GramSymbol) (w : Chromogram) : matchg lb [c] (s :: s' :: w) = false := by
  rw [matchg_cons]
  cases matchStep c s lb <;> simp

theorem balanced_cgram_cons {d : ℕ} {b : Bool} {s : GramSymbol} {w : Chromogram}
    (h : balanced d b (cgram d b (s :: w))) :
    balanced (cgramDepth s d) (cgramBit s b) (cgram (cgramDepth s d) (cgramBit s b) w) := by
  rw [cgram_cons] at h
  cases s with
  | push => exact h
  | skip => exact h
  | pop0 => cases d with
    | zero => simp at h
    | succ n => exact h
  | pop1 => cases d with
    | zero => simp at h
    | succ n => exact h

/-- The generalised form of the reference's `matchg_pg`: matching a completed
trace against a completed chromogram is the same as matching the partial forms. -/
theorem matchg_cgram_eq_matchpg :
    ∀ (et : List Color) (lb : List Bool) (b : Bool) (w : Chromogram),
      balanced lb.length b (cgram lb.length b w) →
      matchg lb (et ++ [closingColor lb b + et.sum]) (cgram lb.length b w)
        = matchpg lb et w := by
  intro et
  induction et with
  | nil =>
    intro lb b w hbal
    simp only [List.nil_append, List.sum_nil, add_zero]
    cases w with
    | cons s w =>
      obtain ⟨s', w', hw⟩ :
          ∃ s' w', cgram (cgramDepth s lb.length) (cgramBit s b) w = s' :: w' := by
        cases hc : cgram (cgramDepth s lb.length) (cgramBit s b) w with
        | nil => exact absurd hc (cgram_ne_nil _ _ _)
        | cons s' w' => exact ⟨s', w', rfl⟩
      rw [cgram_cons, hw, matchg_singleton_of_cons_cons, matchpg_nil_cons]
    | nil =>
      simp only [matchpg_nil]
      rcases lb with _ | ⟨c, lb⟩
      · have hb : b = true := by revert hbal; cases b <;> decide
        subst hb
        decide
      · have hn : lb.length = 0 := by
          simp only [List.length_cons, cgram] at hbal
          rw [ite_eq_right (by omega)] at hbal
          cases b <;> simpa using hbal
        have hlb : lb = [] := List.length_eq_zero_iff.mp hn
        subst hlb
        revert hbal
        cases c <;> cases b <;> decide
  | cons e et ih =>
    intro lb b w hbal
    cases w with
    | nil =>
      rw [cgram, matchpg_cons_nil, List.cons_append, matchg_cons]
      cases matchStep e (if lb.length = 0 then GramSymbol.skip
          else if b then GramSymbol.pop1 else GramSymbol.pop0) lb <;> simp
    | cons s w =>
      have hbal' := balanced_cgram_cons hbal
      rw [cgram_cons, matchpg_cons, List.cons_append, matchg_cons]
      cases hs : matchStep e s lb with
      | none => simp
      | some lb' =>
        simp only [Option.elim]
        have hlen := matchStep_length hs
        have hcol := closingColor_step b hs
        rw [← hlen] at hbal' ⊢
        rw [List.sum_cons, ← add_assoc, ← hcol]
        exact ih lb' (cgramBit s b) w hbal'

/-- Matching a completed trace against a completed chromogram is the same as
matching the partial forms. -/
theorem matchg_completeTrace (et : List Color) (w : Chromogram)
    (hbal : balanced 0 false (cgram 0 false w)) :
    matchg [] (completeTrace et) (cgram 0 false w) = matchpg [] et w := by
  have h := matchg_cgram_eq_matchpg et [] false w (by simpa using hbal)
  simpa [completeTrace, closingColor, Color.ofBits] using h

end FourColor

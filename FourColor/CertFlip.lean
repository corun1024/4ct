import FourColor.Chromogram

/-!
# Flipping a chord preserves matching

Why a certificate answer is a *bit mask* rather than a trace.

The traces matching a chromogram `w` are exactly the `c2`/`c3` flips of any one
of them over unions of `w`'s chords: swapping `c2` for `c3` at both ends of a
chord leaves the chromogram matched, and nothing else does.  So every answer at
a leaf of a certificate is a flip of that leaf's own trace, and the emitter can
store one bit per position instead of a trace — which is what
`FourColor.Answer` does and what makes the certificate data small enough to
elaborate.

Only the direction the checker needs is proved here: if a mask flips both ends
of every chord and nothing at a `skip`, the flipped trace still matches.
`flipOk` is defined by the same recursion the checker performs, so the
induction in `matchg_flip` follows it step for step.

## Main results

* `matchg_flip` — a chord-respecting flip of a matching trace still matches.
-/

namespace FourColor

open Color

def flipC : Bool → Color → Color
  | false, c => c
  | true, .c2 => .c3
  | true, .c3 => .c2
  | true, c => c

/-- Swap `c2`/`c3` at the mask's set positions, counting from `i`. -/
def flipFromB (m : Nat) : Nat → List Color → List Color
  | _, [] => []
  | i, c :: cs => flipC (m.testBit i) c :: flipFromB m (i + 1) cs

/-- `fb` carries the flip bit of each open chord, alongside `lb`'s colour bits. -/
def flipOk (m : Nat) : Nat → List Bool → Chromogram → Bool
  | _, fb, [] => fb.isEmpty
  | i, fb, .skip :: w => !(m.testBit i) && flipOk m (i + 1) fb w
  | i, fb, .push :: w => flipOk m (i + 1) (m.testBit i :: fb) w
  | _, [], .pop0 :: _ => false
  | i, b :: fb, .pop0 :: w => (m.testBit i == b) && flipOk m (i + 1) fb w
  | _, [], .pop1 :: _ => false
  | i, b :: fb, .pop1 :: w => (m.testBit i == b) && flipOk m (i + 1) fb w

/-- A push always succeeds; flipping the colour flips the pushed bit. -/
theorem push_flip (b : Bool) (c : Color) (lb lb2 tail : List Bool)
    (h : matchStep c .push lb = some lb2) :
    ∃ x, lb2 = x :: lb ∧
      matchStep (flipC b c) .push tail = some (xor x b :: tail) := by
  cases c <;> cases b <;> simp_all [matchStep, flipC]

/-- A pop succeeds on the flipped trace with the *same* symbol exactly when both
ends of the chord carry the same flip bit. -/
theorem pop_flip (s : GramSymbol) (hs : s = .pop0 ∨ s = .pop1) (b : Bool) (c : Color)
    (x : Bool) (lb3 lb2 tail : List Bool)
    (h : matchStep c s (x :: lb3) = some lb2) :
    lb2 = lb3 ∧ matchStep (flipC b c) s (xor x b :: tail) = some tail := by
  rcases hs with rfl | rfl <;> cases c <;> cases b <;> cases x <;>
    simp_all [matchStep, flipC]

/-- A pop needs a nonempty stack. -/
theorem pop_stack (s : GramSymbol) (hs : s = .pop0 ∨ s = .pop1) (c : Color)
    (lb lb2 : List Bool) (h : matchStep c s lb = some lb2) :
    ∃ x lb3, lb = x :: lb3 := by
  cases lb with
  | cons x lb3 => exact ⟨x, lb3, rfl⟩
  | nil => rcases hs with rfl | rfl <;> cases c <;> simp [matchStep] at h

/-- **(a)** If the mask flips both ends of every chord of `w` and nothing at a
`skip`, the flipped trace still matches `w`. -/
theorem matchg_flip (m : Nat) :
    ∀ (w : Chromogram) (u : List Color) (i : Nat) (lb fb : List Bool),
      matchg lb u w = true → flipOk m i fb w = true →
      matchg (List.zipWith xor lb fb) (flipFromB m i u) w = true := by
  intro w
  induction w with
  | nil =>
    intro u i lb fb hm hf
    cases u with
    | cons c cs => simp [matchg] at hm
    | nil =>
      simp only [matchg, List.isEmpty_iff] at hm
      subst hm
      simp only [flipOk, List.isEmpty_iff] at hf
      subst hf
      simp [flipFromB, matchg]
  | cons s w ih =>
    intro u i lb fb hm hf
    cases u with
    | nil => simp [matchg] at hm
    | cons c cs =>
      rw [matchg] at hm
      cases hstep : matchStep c s lb with
      | none => rw [hstep] at hm; simp at hm
      | some lb2 =>
        rw [hstep] at hm; simp only [Option.elim] at hm
        rw [flipFromB, matchg]
        cases s with
        | skip =>
          simp only [flipOk, Bool.and_eq_true] at hf
          have hc : c = Color.c1 := by cases c <;> simp_all [matchStep]
          have hlb : lb2 = lb := by cases c <;> simp_all [matchStep]
          subst hc
          rw [hlb] at hm
          have hb : m.testBit i = false := by simpa using hf.1
          rw [hb]
          simp only [flipC, matchStep, Option.elim]
          exact ih cs (i + 1) lb fb hm hf.2
        | push =>
          simp only [flipOk] at hf
          obtain ⟨x, rfl, hstep'⟩ :=
            push_flip (m.testBit i) c lb lb2 (List.zipWith xor lb fb) hstep
          rw [hstep']
          simp only [Option.elim]
          have hrec := ih cs (i + 1) (x :: lb) (m.testBit i :: fb) hm hf
          simpa using hrec
        | pop0 =>
          cases fb with
          | nil => simp [flipOk] at hf
          | cons b fb =>
            simp only [flipOk, Bool.and_eq_true, beq_iff_eq] at hf
            obtain ⟨hbi, hrest⟩ := hf
            obtain ⟨x, lb3, hlb⟩ :=
              pop_stack .pop0 (Or.inl rfl) c lb lb2 hstep
            subst hlb
            have hpf := pop_flip .pop0 (Or.inl rfl) b c x lb3 lb2
              (List.zipWith xor lb3 fb) hstep
            rw [hpf.1] at hm
            rw [hbi]
            simp only [List.zipWith_cons_cons, hpf.2, Option.elim]
            exact ih cs (i + 1) lb3 fb hm hrest
        | pop1 =>
          cases fb with
          | nil => simp [flipOk] at hf
          | cons b fb =>
            simp only [flipOk, Bool.and_eq_true, beq_iff_eq] at hf
            obtain ⟨hbi, hrest⟩ := hf
            obtain ⟨x, lb3, hlb⟩ :=
              pop_stack .pop1 (Or.inr rfl) c lb lb2 hstep
            subst hlb
            have hpf := pop_flip .pop1 (Or.inr rfl) b c x lb3 lb2
              (List.zipWith xor lb3 fb) hstep
            rw [hpf.1] at hm
            rw [hbi]
            simp only [List.zipWith_cons_cons, hpf.2, Option.elim]
            exact ih cs (i + 1) lb3 fb hm hrest

end FourColor

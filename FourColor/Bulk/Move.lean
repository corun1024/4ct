import FourColor.Bulk.Digits

/-!
# Moving digit blocks

The bulk operations of the reducibility check all have the same shape: select
the traces whose digits at one or two positions have given values, and move
that block to where the traces with other values at those positions live.  In
the index space that is a single shift by a signed amount.

* `setDigit p d i` — index `i` with digit `p` replaced by `d`.
* `move1 m p v u M` — the traces of `M` with digit `p` equal to `v`, moved to
  digit value `u`.
* `move2 m p q v w u x M` — the same for two digit positions at once.
* `permDigit m p σ M` — digit `p` of every trace of `M` permuted by `σ`.

Each is characterised bit by bit: bit `i` of the moved block is bit
`setDigit p v i` of `M`, provided digit `p` of `i` is the target value.
-/

namespace FourColor
namespace Bulk

/-! ### Replacing a digit -/

/-- Index `i` with digit `p` set to `d`. -/
def setDigit (p d i : ℕ) : ℕ := i / 3 ^ (p + 1) * 3 ^ (p + 1) + d * 3 ^ p + i % 3 ^ p

theorem digit_setDigit_self {p d : ℕ} (hd : d < 3) (i : ℕ) : digit p (setDigit p d i) = d :=
  digit_of_decomp hd (Nat.mod_lt _ (by positivity))

theorem setDigit_digit_self (p i : ℕ) : setDigit p (digit p i) i = i := (decomp p i).symm

theorem setDigit_lt {m p d i : ℕ} (hp : p < m) (hd : d < 3) (hi : i < 3 ^ m) :
    setDigit p d i < 3 ^ m :=
  lt_of_hi_lt hp (hi_lt hp hi) hd (Nat.mod_lt _ (by positivity))

theorem digit_setDigit_of_ne {p q d : ℕ} (hqp : q ≠ p) (hd : d < 3) (i : ℕ) :
    digit q (setDigit p d i) = digit q i := by
  have hlo := Nat.mod_lt i (show 0 < 3 ^ p by positivity)
  rw [setDigit, digit_decomp_of_ne hqp hd hlo]
  conv_rhs => rw [decomp p i, digit_decomp_of_ne hqp (digit_lt p i) hlo]

theorem setDigit_setDigit (p d e i : ℕ) (hd : d < 3) (he : e < 3) :
    setDigit p d (setDigit p e i) = setDigit p d i := by
  have hlo := Nat.mod_lt i (show 0 < 3 ^ p by positivity)
  unfold setDigit
  rw [hi_of_decomp he hlo, mod_of_decomp hlo]

/-- Changing digit `p` from `v` to `u` shifts the index by `(u - v) * 3 ^ p`. -/
theorem setDigit_eq_add {p v u i : ℕ} (hv : digit p i = v) :
    (setDigit p u i : ℤ) = i + (u - v : ℤ) * 3 ^ p := by
  have hdec := decomp p i
  rw [hv] at hdec
  unfold setDigit
  push_cast
  conv_rhs => rw [hdec]
  push_cast
  ring

/-! ### Signed shifts -/

/-- Shift by a signed amount: left for `0 ≤ δ`, right otherwise. -/
def shiftBy (M : ℕ) (δ : ℤ) : ℕ := if 0 ≤ δ then M <<< δ.toNat else M >>> (-δ).toNat

theorem testBit_shiftBy (M : ℕ) (δ : ℤ) (i : ℕ) :
    (shiftBy M δ).testBit i = (decide (0 ≤ (i : ℤ) - δ) && M.testBit ((i : ℤ) - δ).toNat) := by
  unfold shiftBy
  split_ifs with h
  · rw [Nat.testBit_shiftLeft]
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, δ = d := ⟨δ.toNat, by omega⟩
    simp only [Int.toNat_natCast]
    by_cases hd : d ≤ i
    · have h1 : decide (d ≤ i) = true := by simpa using hd
      have h2 : decide (0 ≤ (i : ℤ) - d) = true := by simp; omega
      have h3 : ((i : ℤ) - d).toNat = i - d := by omega
      rw [h1, h2, h3]
    · have h1 : decide (d ≤ i) = false := by simpa using hd
      have h2 : decide (0 ≤ (i : ℤ) - d) = false := by simp; omega
      rw [h1, h2]; simp
  · rw [Nat.testBit_shiftRight]
    obtain ⟨d, hd⟩ : ∃ d : ℕ, δ = -d := ⟨(-δ).toNat, by omega⟩
    subst hd
    have h2 : decide (0 ≤ (i : ℤ) - -d) = true := by simp; omega
    have h3 : ((i : ℤ) - -(d : ℤ)).toNat = d + i := by omega
    rw [h2, h3, Int.neg_neg, Int.toNat_natCast]; simp

/-! ### Moving one digit block -/

/-- The traces of `M` whose digit `p` is `v`, moved so that their digit `p` is `u`. -/
def move1 (m p v u : ℕ) (M : ℕ) : ℕ :=
  shiftBy (M &&& sel m p v) ((u - v : ℤ) * 3 ^ p)

theorem testBit_move1 {m p v u : ℕ} (hp : p < m) (hv : v < 3) (hu : u < 3) (M i : ℕ)
    (hi : i < 3 ^ m) :
    (move1 m p v u M).testBit i = (decide (digit p i = u) && M.testBit (setDigit p v i)) := by
  unfold move1
  rw [testBit_shiftBy]
  by_cases hdi : digit p i = u
  · -- the source index is `setDigit p v i`, one shift away
    have hj : (setDigit p v i : ℤ) = i + (v - u : ℤ) * 3 ^ p := setDigit_eq_add hdi
    have h0 : 0 ≤ (i : ℤ) - (u - v : ℤ) * 3 ^ p := by
      have := Nat.zero_le (setDigit p v i); push_cast at this ⊢; linarith
    have hsrc : ((i : ℤ) - (u - v : ℤ) * 3 ^ p).toNat = setDigit p v i := by
      have : ((i : ℤ) - (u - v : ℤ) * 3 ^ p) = setDigit p v i := by rw [hj]; ring
      rw [this, Int.toNat_natCast]
    have h0' : decide (0 ≤ (i : ℤ) - (u - v : ℤ) * 3 ^ p) = true := by simpa using h0
    rw [hsrc, h0', Nat.testBit_and, testBit_sel hp v hv]
    simp [hdi, setDigit_lt hp hv hi, digit_setDigit_self hv]
  · -- no block lands here: a source with digit `v` would have to shift to digit `u`
    simp only [hdi, decide_false, Bool.false_and]
    by_cases h0 : 0 ≤ (i : ℤ) - (u - v : ℤ) * 3 ^ p
    · rw [Nat.testBit_and, testBit_sel hp v hv]
      set j := ((i : ℤ) - (u - v : ℤ) * 3 ^ p).toNat with hjdef
      have hsel : decide (j < 3 ^ m ∧ digit p j = v) = false := by
        simp only [decide_eq_false_iff_not]
        rintro ⟨-, hdig⟩
        have hij : (i : ℤ) = j + (u - v : ℤ) * 3 ^ p := by rw [hjdef]; omega
        have := setDigit_eq_add (u := u) hdig
        have hij' : (i : ℤ) = setDigit p u j := by rw [this]; exact hij
        have hiu : i = setDigit p u j := by exact_mod_cast hij'
        exact hdi (by rw [hiu, digit_setDigit_self hu])
      rw [hsel]; simp
    · have h0' : decide (0 ≤ (i : ℤ) - (u - v : ℤ) * 3 ^ p) = false := by simpa using h0
      rw [h0']; simp

/-! ### Moving a two-digit block -/

/-- The traces of `M` with digits `v` at `p` and `w` at `q`, moved to digits `u` and `x`. -/
def move2 (m p q v w u x : ℕ) (M : ℕ) : ℕ :=
  shiftBy (M &&& sel m p v &&& sel m q w) ((u - v : ℤ) * 3 ^ p + (x - w : ℤ) * 3 ^ q)

theorem testBit_move2 {m p q v w u x : ℕ} (hp : p < m) (hq : q < m) (hpq : p ≠ q)
    (hv : v < 3) (hw : w < 3) (hu : u < 3) (hx : x < 3) (M i : ℕ) (hi : i < 3 ^ m) :
    (move2 m p q v w u x M).testBit i =
      (decide (digit p i = u ∧ digit q i = x) && M.testBit (setDigit p v (setDigit q w i))) := by
  unfold move2
  rw [testBit_shiftBy]
  set δ : ℤ := (u - v : ℤ) * 3 ^ p + (x - w : ℤ) * 3 ^ q with hδ
  -- the two-digit replacement is one shift
  have key : ∀ j, digit p j = v → digit q j = w →
      (setDigit p u (setDigit q x j) : ℤ) = j + δ := by
    intro j hjp hjq
    have h1 : (setDigit q x j : ℤ) = j + (x - w : ℤ) * 3 ^ q := setDigit_eq_add hjq
    have h2 : digit p (setDigit q x j) = v := by rw [digit_setDigit_of_ne hpq hx, hjp]
    have h3 : (setDigit p u (setDigit q x j) : ℤ) = setDigit q x j + (u - v : ℤ) * 3 ^ p :=
      setDigit_eq_add h2
    rw [h3, h1, hδ]; ring
  by_cases hdi : digit p i = u ∧ digit q i = x
  · obtain ⟨hpu, hqx⟩ := hdi
    set j := setDigit p v (setDigit q w i) with hjdef
    have hjp : digit p j = v := digit_setDigit_self hv _
    have hjq : digit q j = w := by
      rw [hjdef, digit_setDigit_of_ne hpq.symm hv, digit_setDigit_self hw]
    have hjlt : j < 3 ^ m := setDigit_lt hp hv (setDigit_lt hq hw hi)
    have hback : setDigit p u (setDigit q x j) = i := by
      apply digits_ext (setDigit_lt hp hu (setDigit_lt hq hx hjlt)) hi
      intro r
      by_cases hr : r = p
      · subst hr; rw [digit_setDigit_self hu, hpu]
      by_cases hr' : r = q
      · subst hr'; rw [digit_setDigit_of_ne hr hu, digit_setDigit_self hx, hqx]
      · rw [digit_setDigit_of_ne hr hu, digit_setDigit_of_ne hr' hx, hjdef,
          digit_setDigit_of_ne hr hv, digit_setDigit_of_ne hr' hw]
    have hij : (i : ℤ) = j + δ := by rw [← hback, key j hjp hjq]
    have h0 : decide (0 ≤ (i : ℤ) - δ) = true := by simp; rw [hij]; omega
    have hsrc : ((i : ℤ) - δ).toNat = j := by rw [hij]; omega
    rw [hsrc, h0, Nat.testBit_and, Nat.testBit_and, testBit_sel hp v hv, testBit_sel hq w hw]
    simp [hpu, hqx, hjlt, hjp, hjq]
  · simp only [hdi, decide_false, Bool.false_and]
    by_cases h0 : 0 ≤ (i : ℤ) - δ
    · rw [Nat.testBit_and, Nat.testBit_and, testBit_sel hp v hv, testBit_sel hq w hw]
      set j := ((i : ℤ) - δ).toNat with hjdef
      have hne : ¬ (j < 3 ^ m ∧ digit p j = v ∧ digit q j = w) := by
        rintro ⟨-, hjp, hjq⟩
        have hij : (i : ℤ) = j + δ := by rw [hjdef]; omega
        have : (i : ℤ) = setDigit p u (setDigit q x j) := by rw [key j hjp hjq]; exact hij
        have hi' : i = setDigit p u (setDigit q x j) := by exact_mod_cast this
        apply hdi
        rw [hi', digit_setDigit_self hu, digit_setDigit_of_ne hpq.symm hu, digit_setDigit_self hx]
        exact ⟨rfl, rfl⟩
      by_cases hlt : j < 3 ^ m
      · by_cases hjp : digit p j = v
        · have hjq : ¬ digit q j = w := fun h => hne ⟨hlt, hjp, h⟩
          simp [hjq]
        · simp [hjp]
      · simp [hlt]
    · have h0' : decide (0 ≤ (i : ℤ) - δ) = false := by simpa using h0
      rw [h0']; simp

/-! ### Permuting a digit -/

/-- Digit `p` of every trace of `M` sent through `σ`. -/
def permDigit (m p : ℕ) (σ : ℕ → ℕ) (M : ℕ) : ℕ :=
  move1 m p 0 (σ 0) M ||| move1 m p 1 (σ 1) M ||| move1 m p 2 (σ 2) M

/-- `σ` permutes `{0, 1, 2}`, with inverse `τ`. -/
structure DigitPerm (σ τ : ℕ → ℕ) : Prop where
  lt : ∀ d, d < 3 → σ d < 3
  left_inv : ∀ d, d < 3 → τ (σ d) = d
  right_inv : ∀ d, d < 3 → σ (τ d) = d
  tau_lt : ∀ d, d < 3 → τ d < 3

theorem testBit_permDigit {m p : ℕ} (hp : p < m) {σ τ : ℕ → ℕ} (h : DigitPerm σ τ) (M i : ℕ)
    (hi : i < 3 ^ m) :
    (permDigit m p σ M).testBit i = M.testBit (setDigit p (τ (digit p i)) i) := by
  unfold permDigit
  rw [Nat.testBit_or, Nat.testBit_or,
    testBit_move1 hp (by norm_num) (h.lt 0 (by norm_num)) M i hi,
    testBit_move1 hp (by norm_num) (h.lt 1 (by norm_num)) M i hi,
    testBit_move1 hp (by norm_num) (h.lt 2 (by norm_num)) M i hi]
  have hd := digit_lt p i
  set d := digit p i with hd'
  -- exactly one of the three blocks lands on digit `d`
  have hτ : τ d < 3 := h.tau_lt d hd
  have hστ : σ (τ d) = d := h.right_inv d hd
  have huniq : ∀ v, v < 3 → σ v = d → v = τ d := by
    intro v hv hvd; rw [← hvd, h.left_inv v hv]
  rcases (show τ d = 0 ∨ τ d = 1 ∨ τ d = 2 by omega) with h0 | h1 | h2
  · rw [h0] at hστ ⊢
    have n1 : σ 1 ≠ d := fun e => by have := huniq 1 (by norm_num) e; omega
    have n2 : σ 2 ≠ d := fun e => by have := huniq 2 (by norm_num) e; omega
    simp [hστ, n1, n2, n1.symm, n2.symm]
  · rw [h1] at hστ ⊢
    have n0 : σ 0 ≠ d := fun e => by have := huniq 0 (by norm_num) e; omega
    have n2 : σ 2 ≠ d := fun e => by have := huniq 2 (by norm_num) e; omega
    simp [hστ, n0, n2, n0.symm, n2.symm]
  · rw [h2] at hστ ⊢
    have n0 : σ 0 ≠ d := fun e => by have := huniq 0 (by norm_num) e; omega
    have n1 : σ 1 ≠ d := fun e => by have := huniq 1 (by norm_num) e; omega
    simp [hστ, n0, n1, n0.symm, n1.symm]

end Bulk
end FourColor

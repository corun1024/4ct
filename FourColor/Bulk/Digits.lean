import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import FourColor.Color

/-!
# Sets of ring traces as bitmasks over base-3 digits

A ring trace of length `n` is determined by its first `m = n - 1` colours, the
last being the sum of the others.  Reading those colours as base-3 digits gives
every trace an index below `3 ^ m`, and a *set* of traces becomes a single
natural number: bit `i` is set when trace `i` is in the set.

The point of the encoding is that the operations the reducibility check needs
are block moves on the index space, so they cost a handful of `Nat` primitives
however many traces are involved:

* `sel m p d` — the traces whose digit `p` is `d`; a periodic pattern built by
  doubling (`rep`).
* `tog m p M` — the set `M` with colours `c2` and `c3` swapped at position `p`,
  which is the digit values `1` and `2` swapped: two block shifts.
* `xacc m p` — the traces sorted by the sum of their first `p` colours, from
  which the colour at the completing position `m` is read off.

Everything is characterised bit by bit (`testBit_sel`, `testBit_tog`,
`testBit_xacc`), which is all the soundness proofs consume.
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Digits -/

/-- Digit `p` of `i` in base 3. -/
def digit (p i : ℕ) : ℕ := i / 3 ^ p % 3

theorem digit_lt (p i : ℕ) : digit p i < 3 := Nat.mod_lt _ (by norm_num)

/-- The colour a digit stands for: `0 ↦ c1`, `1 ↦ c2`, `2 ↦ c3`. -/
def colourOfDigit : ℕ → Color
  | 0 => c1
  | 1 => c2
  | _ => c3

/-- The first `m` colours of trace `i`. -/
def partialOf (m i : ℕ) : List Color := (List.range m).map fun p => colourOfDigit (digit p i)

/-- Trace `i`: its `m` digits completed by their sum. -/
def traceOf (m i : ℕ) : List Color := completeTrace (partialOf m i)

@[simp] theorem length_partialOf (m i : ℕ) : (partialOf m i).length = m := by
  simp [partialOf]

@[simp] theorem length_traceOf (m i : ℕ) : (traceOf m i).length = m + 1 := by
  simp [traceOf]

theorem getElem_partialOf (m i p : ℕ) (hp : p < m) :
    (partialOf m i)[p]'(by simpa using hp) = colourOfDigit (digit p i) := by
  simp [partialOf]

/-- Every index decomposes around digit `p`. -/
theorem decomp (p i : ℕ) :
    i = i / 3 ^ (p + 1) * 3 ^ (p + 1) + digit p i * 3 ^ p + i % 3 ^ p := by
  have h1 := Nat.div_add_mod i (3 ^ p)
  have h2 := Nat.div_add_mod (i / 3 ^ p) 3
  have h3 : i / 3 ^ (p + 1) = i / 3 ^ p / 3 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  unfold digit
  rw [h3, Nat.pow_succ]
  calc i = 3 ^ p * (i / 3 ^ p) + i % 3 ^ p := h1.symm
    _ = 3 ^ p * (3 * (i / 3 ^ p / 3) + i / 3 ^ p % 3) + i % 3 ^ p := by rw [h2]
    _ = i / 3 ^ p / 3 * (3 ^ p * 3) + i / 3 ^ p % 3 * 3 ^ p + i % 3 ^ p := by ring

theorem digit_of_decomp {p hi d lo : ℕ} (hd : d < 3) (hlo : lo < 3 ^ p) :
    digit p (hi * 3 ^ (p + 1) + d * 3 ^ p + lo) = d := by
  unfold digit
  have hpos : 0 < 3 ^ p := by positivity
  rw [show hi * 3 ^ (p + 1) + d * 3 ^ p + lo = lo + (hi * 3 + d) * 3 ^ p by
        rw [Nat.pow_succ]; ring,
      Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
  omega

theorem mod_of_decomp {p hi d lo : ℕ} (hlo : lo < 3 ^ p) :
    (hi * 3 ^ (p + 1) + d * 3 ^ p + lo) % 3 ^ p = lo := by
  rw [show hi * 3 ^ (p + 1) + d * 3 ^ p + lo = lo + (hi * 3 + d) * 3 ^ p by
        rw [Nat.pow_succ]; ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo]

theorem hi_of_decomp {p hi d lo : ℕ} (hd : d < 3) (hlo : lo < 3 ^ p) :
    (hi * 3 ^ (p + 1) + d * 3 ^ p + lo) / 3 ^ (p + 1) = hi := by
  have hpos : 0 < 3 ^ (p + 1) := by positivity
  have hlt : d * 3 ^ p + lo < 3 ^ (p + 1) := by rw [Nat.pow_succ]; nlinarith
  rw [show hi * 3 ^ (p + 1) + d * 3 ^ p + lo = (d * 3 ^ p + lo) + hi * 3 ^ (p + 1) by ring,
      Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- Below `3 ^ m` the high part is below `3 ^ (m - p - 1)`. -/
theorem hi_lt {m p i : ℕ} (hp : p < m) (hi : i < 3 ^ m) :
    i / 3 ^ (p + 1) < 3 ^ (m - p - 1) := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
  have : m - p - 1 + (p + 1) = m := by omega
  rw [this]; exact hi

theorem lt_of_hi_lt {m p hi d lo : ℕ} (hp : p < m) (hhi : hi < 3 ^ (m - p - 1))
    (hd : d < 3) (hlo : lo < 3 ^ p) :
    hi * 3 ^ (p + 1) + d * 3 ^ p + lo < 3 ^ m := by
  have h1 : d * 3 ^ p + lo < 3 ^ (p + 1) := by rw [Nat.pow_succ]; nlinarith
  have h2 : (hi + 1) * 3 ^ (p + 1) ≤ 3 ^ (m - p - 1) * 3 ^ (p + 1) :=
    Nat.mul_le_mul_right _ hhi
  rw [← Nat.pow_add] at h2
  have : m - p - 1 + (p + 1) = m := by omega
  rw [this] at h2
  nlinarith

/-! ### Repeating a pattern -/

/-- `rep x w f k` is `x` (a pattern of width `w`) repeated `k` times, built by
doubling; `f` is fuel, any `f` with `k < 2 ^ f`. -/
def rep (x w : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, k =>
    if k = 0 then 0 else
      let y := rep x w f (k / 2)
      let yy := y ||| (y <<< (w * (k / 2)))
      if k % 2 = 0 then yy else x ||| (yy <<< w)

theorem testBit_rep (x w : ℕ) (hx : x < 2 ^ w) :
    ∀ (f k i : ℕ), k < 2 ^ f →
      (rep x w f k).testBit i = (decide (i < w * k) && x.testBit (i % w)) := by
  intro f
  induction f with
  | zero =>
    intro k i hk
    have : k = 0 := by simpa using hk
    subst this
    simp [rep]
  | succ f ih =>
    intro k i hk
    by_cases hk0 : k = 0
    · subst hk0; simp [rep]
    rw [rep, if_neg hk0]
    have hk2 : k / 2 < 2 ^ f := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← Nat.pow_succ]; exact hk
    have hy := ih (k / 2)
    -- name the nonlinear atoms
    set s := w * (k / 2) with hs
    have hs2 : w * (2 * (k / 2)) = 2 * s := by rw [hs]; ring
    -- the doubled pattern
    have hyy : ∀ j, (rep x w f (k / 2) ||| (rep x w f (k / 2) <<< s)).testBit j
        = (decide (j < 2 * s) && x.testBit (j % w)) := by
      intro j
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, hy j hk2, hy _ hk2]
      by_cases hj : s ≤ j
      · have hmod : (j - s) % w = j % w := by
          rw [hs]; exact Nat.sub_mul_mod (by rw [← hs]; exact hj)
        rw [hmod]
        have h1 : decide (j < s) = false := by simp; omega
        have h2 : decide (s ≤ j) = true := by simpa using hj
        rw [h1, h2]
        have h3 : decide (j - s < s) = decide (j < 2 * s) := by
          simp only [decide_eq_decide]; omega
        rw [h3]; simp
      · have h2 : decide (s ≤ j) = false := by simpa using hj
        have h3 : decide (j < s) = decide (j < 2 * s) := by
          simp only [decide_eq_decide]; omega
        rw [h2, h3]; simp
    by_cases hpar : k % 2 = 0
    · rw [if_pos hpar, hyy]
      have : k = 2 * (k / 2) := by omega
      rw [← hs2, ← this]
    · rw [if_neg hpar, Nat.testBit_or, Nat.testBit_shiftLeft, hyy]
      have hk1 : k = 2 * (k / 2) + 1 := by omega
      have hwk : w * k = 2 * s + w := by rw [hk1, Nat.mul_add, hs2, Nat.mul_one]
      rw [hwk]
      by_cases hi : w ≤ i
      · have hx0 : x.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))
        have h2 : decide (w ≤ i) = true := by simpa using hi
        have hmod : (i - w) % w = i % w := by
          have := Nat.sub_mul_mod (x := i) (k := 1) (n := w) (by simpa using hi)
          simpa using this
        have h3 : decide (i - w < 2 * s) = decide (i < 2 * s + w) := by
          simp only [decide_eq_decide]; omega
        rw [hx0, h2, hmod, h3]; simp
      · have h2 : decide (w ≤ i) = false := by simpa using hi
        have hlt : decide (i < 2 * s + w) = true := by simp; omega
        have hmod : i % w = i := Nat.mod_eq_of_lt (by omega)
        rw [h2, hlt, hmod]; simp

/-! ### Digit selectors -/

/-- The traces (indices below `3 ^ m`) whose digit `p` is `d`, for `p < m`. -/
def sel (m p d : ℕ) : ℕ :=
  rep ((2 ^ 3 ^ p - 1) <<< (d * 3 ^ p)) (3 ^ (p + 1)) (2 * m + 2) (3 ^ (m - p - 1))

theorem three_pow_lt_two_pow (k : ℕ) : 3 ^ k < 2 ^ (2 * k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have : 2 * (k + 1) + 2 = 2 * k + 2 + 2 := by ring
    rw [this, Nat.pow_succ, Nat.pow_add]
    omega

theorem testBit_sel {m p : ℕ} (hp : p < m) (d : ℕ) (hd : d < 3) (i : ℕ) :
    (sel m p d).testBit i = decide (i < 3 ^ m ∧ digit p i = d) := by
  unfold sel
  have hx : (2 ^ 3 ^ p - 1) <<< (d * 3 ^ p) < 2 ^ 3 ^ (p + 1) := by
    rw [Nat.shiftLeft_eq, Nat.pow_succ]
    have h1 : 2 ^ 3 ^ p - 1 < 2 ^ 3 ^ p := Nat.sub_lt (by positivity) (by norm_num)
    calc (2 ^ 3 ^ p - 1) * 2 ^ (d * 3 ^ p) < 2 ^ 3 ^ p * 2 ^ (d * 3 ^ p) :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ (3 ^ p + d * 3 ^ p) := by rw [← Nat.pow_add]
      _ ≤ 2 ^ (3 ^ p * 3) := Nat.pow_le_pow_right (by norm_num) (by
          have := Nat.mul_le_mul_right (3 ^ p) (show d ≤ 2 by omega); omega)
  have hk : 3 ^ (m - p - 1) < 2 ^ (2 * m + 2) :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) (three_pow_lt_two_pow m)
  rw [testBit_rep _ _ hx _ _ i hk, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  have hw : 3 ^ (p + 1) * 3 ^ (m - p - 1) = 3 ^ m := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hw]
  -- the pattern picks out the block of digit `d`
  have hpos : 0 < 3 ^ p := by positivity
  have hr : i % 3 ^ (p + 1) = digit p i * 3 ^ p + i % 3 ^ p := by
    conv_lhs => rw [decomp p i]
    rw [Nat.pow_succ]
    rw [show i / (3 ^ p * 3) * (3 ^ p * 3) + digit p i * 3 ^ p + i % 3 ^ p
        = (digit p i * 3 ^ p + i % 3 ^ p) + i / (3 ^ p * 3) * (3 ^ p * 3) by ring]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
    have := digit_lt p i
    have := Nat.mod_lt i hpos
    nlinarith
  rw [hr]
  have hmod := Nat.mod_lt i hpos
  have hdig := digit_lt p i
  by_cases hi : i < 3 ^ m
  · simp only [hi, true_and, decide_true, Bool.true_and]
    by_cases heq : digit p i = d
    · rw [heq]
      simp only [decide_true]
      have h1 : d * 3 ^ p ≤ d * 3 ^ p + i % 3 ^ p := Nat.le_add_right _ _
      have h2 : d * 3 ^ p + i % 3 ^ p - d * 3 ^ p < 3 ^ p := by omega
      simp [h1, h2, hmod]
    · simp only [heq, decide_false]
      rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
      · have hba : digit p i * 3 ^ p + 3 ^ p ≤ d * 3 ^ p := by
          have := Nat.mul_le_mul_right (3 ^ p) (Nat.succ_le_of_lt hlt)
          rwa [Nat.succ_mul] at this
        have : ¬ (d * 3 ^ p ≤ digit p i * 3 ^ p + i % 3 ^ p) := by omega
        simp [this]
      · have hba : d * 3 ^ p + 3 ^ p ≤ digit p i * 3 ^ p := by
          have := Nat.mul_le_mul_right (3 ^ p) (Nat.succ_le_of_lt hgt)
          rwa [Nat.succ_mul] at this
        have hle : d * 3 ^ p ≤ digit p i * 3 ^ p + i % 3 ^ p := by omega
        have : ¬ (digit p i * 3 ^ p + i % 3 ^ p - d * 3 ^ p < 3 ^ p) := by omega
        simp [hle, this]
  · simp [hi]

/-- Arithmetic of the digit blocks, stated over atoms so `omega` can use it. -/
theorem sub_block21 {X l n : ℕ} : X + 2 * l + n - l = X + 1 * l + n := by omega

theorem sub_block10 {X l n : ℕ} : X + 1 * l + n - l = X + 0 * l + n := by omega

theorem sub_block0 {H l n : ℕ} (hH : 0 < H) :
    H * (l * 3) + 0 * l + n - l = (H - 1) * (l * 3) + 2 * l + n := by
  obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (H' + 1) * (l * 3) = H' * (l * 3) + 3 * l by ring]
  omega

/-! ### Toggling a position -/

/-- Swap the digit values `1` and `2` (colours `c2` and `c3`) at position `p`. -/
def togIdx (p i : ℕ) : ℕ :=
  if digit p i = 1 then i + 3 ^ p else if digit p i = 2 then i - 3 ^ p else i

theorem togIdx_lt {m p i : ℕ} (hp : p < m) (hi : i < 3 ^ m) : togIdx p i < 3 ^ m := by
  unfold togIdx
  have hd := digit_lt p i
  have hhi := hi_lt hp hi
  have hlo := Nat.mod_lt i (show 0 < 3 ^ p by positivity)
  split_ifs with h1 h2
  · conv_lhs => rw [decomp p i]
    rw [h1]
    have := lt_of_hi_lt hp hhi (d := 2) (lo := i % 3 ^ p) (by norm_num) hlo
    linarith
  · exact lt_of_le_of_lt (Nat.sub_le _ _) hi
  · exact hi

theorem togIdx_togIdx {m p i : ℕ} (hp : p < m) (hi : i < 3 ^ m) :
    togIdx p (togIdx p i) = i := by
  have hd := digit_lt p i
  have hlo := Nat.mod_lt i (show 0 < 3 ^ p by positivity)
  have hdec := decomp p i
  unfold togIdx
  by_cases h1 : digit p i = 1
  · rw [if_pos h1]
    have hd' : digit p (i + 3 ^ p) = 2 := by
      conv_lhs => rw [hdec, h1]
      rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p + 3 ^ p
          = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p by ring]
      exact digit_of_decomp (by norm_num) hlo
    rw [hd']; simp
  · rw [if_neg h1]
    by_cases h2 : digit p i = 2
    · rw [if_pos h2]
      have hd' : digit p (i - 3 ^ p) = 1 := by
        conv_lhs => rw [hdec, h2]
        rw [sub_block21]
        exact digit_of_decomp (by norm_num) hlo
      have hle : 3 ^ p ≤ i := by
        conv_rhs => rw [hdec, h2]
        omega
      rw [hd']; simp [Nat.sub_add_cancel hle]
    · rw [if_neg h2, if_neg h1, if_neg h2]

/-- `M` with colours `c2` and `c3` swapped at position `p`. -/
def tog (m p M : ℕ) : ℕ :=
  (M &&& sel m p 0) ||| ((M &&& sel m p 1) <<< 3 ^ p) ||| ((M &&& sel m p 2) >>> 3 ^ p)

theorem testBit_tog {m p : ℕ} (hp : p < m) (M i : ℕ) (hi : i < 3 ^ m) :
    (tog m p M).testBit i = M.testBit (togIdx p i) := by
  unfold tog
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_and,
    testBit_sel hp 0 (by norm_num), testBit_sel hp 1 (by norm_num),
    testBit_sel hp 2 (by norm_num)]
  have hd := digit_lt p i
  have hpos : 0 < 3 ^ p := by positivity
  have hlo := Nat.mod_lt i hpos
  have hdec := decomp p i
  have hhi := hi_lt hp hi
  unfold togIdx
  by_cases h1 : digit p i = 1
  · -- the trace sits in block 1: it comes from block 2 of `M`, i.e. from `i + 3 ^ p`
    rw [if_pos h1]
    have hd2 : digit p (i + 3 ^ p) = 2 := by
      conv_lhs => rw [hdec, h1]
      rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p + 3 ^ p
          = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p by ring]
      exact digit_of_decomp (by norm_num) hlo
    have hlt2 : i + 3 ^ p < 3 ^ m := by
      conv_lhs => rw [hdec, h1]
      rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p + 3 ^ p
          = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p by ring]
      exact lt_of_hi_lt hp hhi (by norm_num) hlo
    have hno1 : ¬ (3 ^ p ≤ i ∧ digit p (i - 3 ^ p) = 1) := by
      rintro ⟨hle, hd1⟩
      have : digit p (i - 3 ^ p) = 0 := by
        conv_lhs => rw [hdec, h1]
        rw [sub_block10]
        exact digit_of_decomp (by norm_num) hlo
      omega
    rw [Nat.add_comm (3 ^ p) i]
    simp only [hi, h1, hd2, hlt2, true_and, and_true, decide_true, Bool.and_true]
    by_cases hle : 3 ^ p ≤ i
    · have : digit p (i - 3 ^ p) ≠ 1 := fun h => hno1 ⟨hle, h⟩
      simp [this]
    · simp [hle]
  · rw [if_neg h1]
    by_cases h2 : digit p i = 2
    · -- block 2 comes from block 1 of `M`, at `i - 3 ^ p`
      rw [if_pos h2]
      have hle : 3 ^ p ≤ i := by rw [hdec, h2]; omega
      have hd1 : digit p (i - 3 ^ p) = 1 := by
        conv_lhs => rw [hdec, h2]
        rw [sub_block21]
        exact digit_of_decomp (by norm_num) hlo
      have hlt1 : i - 3 ^ p < 3 ^ m := lt_of_le_of_lt (Nat.sub_le _ _) hi
      have hno2 : digit p (3 ^ p + i) ≠ 2 := by
        rw [Nat.add_comm]
        conv_lhs => rw [hdec, h2]
        rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p + 3 ^ p
            = (i / 3 ^ (p + 1) + 1) * 3 ^ (p + 1) + 0 * 3 ^ p + i % 3 ^ p by
              rw [Nat.pow_succ]; ring]
        rw [digit_of_decomp (by norm_num) hlo]; omega
      simp [hi, h1, h2, hle, hd1, hlt1, hno2]
    · rw [if_neg h2]
      have h0 : digit p i = 0 := by omega
      have hno1 : ¬ (3 ^ p ≤ i ∧ digit p (i - 3 ^ p) = 1) := by
        rintro ⟨hle, hd1⟩
        have : digit p (i - 3 ^ p) = 2 := by
          conv_lhs => rw [hdec, h0]
          have hhi0 : 0 < i / 3 ^ (p + 1) := by
            by_contra hc
            have : i / 3 ^ (p + 1) = 0 := Nat.eq_zero_of_not_pos hc
            rw [this, h0] at hdec; omega
          set H := i / 3 ^ (p + 1) with hH
          rw [Nat.pow_succ, sub_block0 hhi0, ← Nat.pow_succ]
          exact digit_of_decomp (by norm_num) hlo
        omega
      have hno2 : digit p (3 ^ p + i) ≠ 2 := by
        rw [Nat.add_comm]
        conv_lhs => rw [hdec, h0]
        rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 0 * 3 ^ p + i % 3 ^ p + 3 ^ p
            = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p by ring]
        rw [digit_of_decomp (by norm_num) hlo]; omega
      simp only [hi, h0, true_and, decide_true, Bool.true_and, hno2, and_false, decide_false,
        Bool.and_false, Bool.or_false]
      by_cases hle : 3 ^ p ≤ i
      · have : digit p (i - 3 ^ p) ≠ 1 := fun h => hno1 ⟨hle, h⟩
        simp [this]
      · simp [hle]

/-- The colour at position `p` of trace `i` is `c2` or `c3` exactly when the toggle moves it. -/
theorem togIdx_eq_self_iff {p i : ℕ} : togIdx p i = i ↔ digit p i = 0 := by
  unfold togIdx
  have hpos : 0 < 3 ^ p := by positivity
  have hd := digit_lt p i
  split_ifs with h1 h2
  · constructor
    · intro h; omega
    · intro h; omega
  · constructor
    · intro h
      have hle : 3 ^ p ≤ i := by
        have := decomp p i
        rw [h2] at this; omega
      omega
    · intro h; omega
  · constructor <;> intro _ <;> first | rfl | omega

/-! ### Colours and digits -/

theorem colourOfDigit_ne_zero (d : ℕ) : colourOfDigit d ≠ 0 := by
  unfold colourOfDigit; split <;> decide

theorem colourOfDigit_eq_c1_iff (d : ℕ) : colourOfDigit d = c1 ↔ d = 0 := by
  match d with
  | 0 => simp [colourOfDigit]
  | 1 => exact ⟨fun h => absurd h (by decide), fun h => by omega⟩
  | d + 2 => exact ⟨fun h => absurd (show c3 = c1 from h) (by decide), fun h => by omega⟩

/-- Toggling a position swaps `c2` and `c3` in the colour it holds. -/
theorem colourOfDigit_togIdx (p i : ℕ) :
    colourOfDigit (digit p (togIdx p i)) = EdgePerm.e132 (colourOfDigit (digit p i)) := by
  have hd := digit_lt p i
  have hpos : 0 < 3 ^ p := by positivity
  have hlo := Nat.mod_lt i hpos
  have hdec := decomp p i
  unfold togIdx
  by_cases h1 : digit p i = 1
  · rw [if_pos h1]
    have : digit p (i + 3 ^ p) = 2 := by
      conv_lhs => rw [hdec, h1]
      rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p + 3 ^ p
          = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p by ring]
      exact digit_of_decomp (by norm_num) hlo
    rw [this, h1]; rfl
  · rw [if_neg h1]
    by_cases h2 : digit p i = 2
    · rw [if_pos h2]
      have : digit p (i - 3 ^ p) = 1 := by
        conv_lhs => rw [hdec, h2]
        rw [sub_block21]
        exact digit_of_decomp (by norm_num) hlo
      rw [this, h2]; rfl
    · rw [if_neg h2]
      have h0 : digit p i = 0 := by omega
      rw [h0]; rfl

/-- Digit `q` does not see digit `p`'s value. -/
theorem digit_decomp_of_ne {p q : ℕ} (hqp : q ≠ p) {hi d lo : ℕ} (hd : d < 3) (hlo : lo < 3 ^ p) :
    digit q (hi * 3 ^ (p + 1) + d * 3 ^ p + lo) = digit q (hi * 3 ^ (p + 1) + lo) := by
  rcases Nat.lt_or_gt_of_ne hqp with hq | hq
  · -- q below p: everything from digit p up vanishes modulo 3 after dividing by 3 ^ q
    obtain ⟨c, hc⟩ : 3 ^ (q + 1) ∣ 3 ^ p := Nat.pow_dvd_pow 3 hq
    have hpos' : 0 < 3 ^ q := by positivity
    have key : ∀ K : ℕ, digit q (lo + K * 3 ^ (q + 1)) = lo / 3 ^ q % 3 := by
      intro K
      unfold digit
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.add_mul_div_right _ _ hpos',
        Nat.add_mul_mod_self_right]
    rw [show hi * 3 ^ (p + 1) + d * 3 ^ p + lo = lo + (hi * 3 * c + d * c) * 3 ^ (q + 1) by
          rw [Nat.pow_succ, hc]; ring,
        show hi * 3 ^ (p + 1) + lo = lo + (hi * 3 * c) * 3 ^ (q + 1) by
          rw [Nat.pow_succ, hc]; ring,
        key, key]
  · -- q above p: the digit-p block is below 3 ^ q
    obtain ⟨c, hc⟩ : 3 ^ (p + 1) ∣ 3 ^ q := Nat.pow_dvd_pow 3 hq
    have hlt : d * 3 ^ p + lo < 3 ^ (p + 1) := by rw [Nat.pow_succ]; nlinarith
    have hlt' : lo < 3 ^ (p + 1) := by rw [Nat.pow_succ]; nlinarith
    have hpos' : 0 < 3 ^ (p + 1) := by positivity
    unfold digit
    rw [hc, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      show hi * 3 ^ (p + 1) + d * 3 ^ p + lo = (d * 3 ^ p + lo) + hi * 3 ^ (p + 1) by ring,
      show hi * 3 ^ (p + 1) + lo = lo + hi * 3 ^ (p + 1) by ring,
      Nat.add_mul_div_right _ _ hpos', Nat.add_mul_div_right _ _ hpos',
      Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt hlt']

/-- Two indices below `3 ^ m` with the same digits are equal. -/
theorem digits_ext {m i j : ℕ} (hi : i < 3 ^ m) (hj : j < 3 ^ m)
    (h : ∀ r, digit r i = digit r j) : i = j := by
  induction m generalizing i j with
  | zero => simp at hi hj; omega
  | succ m ih =>
    have hdec_i := decomp m i
    have hdec_j := decomp m j
    have hi' : i / 3 ^ (m + 1) = 0 := Nat.div_eq_of_lt hi
    have hj' : j / 3 ^ (m + 1) = 0 := Nat.div_eq_of_lt hj
    rw [hi', Nat.zero_mul, Nat.zero_add] at hdec_i
    rw [hj', Nat.zero_mul, Nat.zero_add] at hdec_j
    have hlo : i % 3 ^ m = j % 3 ^ m := by
      apply ih (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
      intro r
      by_cases hr : r < m
      · -- digits below m of the remainders agree with those of i and j
        have e1 : digit r (i % 3 ^ m) = digit r i := by
          conv_rhs => rw [hdec_i]
          rw [show digit m i * 3 ^ m + i % 3 ^ m = 0 * 3 ^ (m + 1) + digit m i * 3 ^ m + i % 3 ^ m by ring,
            digit_decomp_of_ne (by omega) (digit_lt m i) (Nat.mod_lt _ (by positivity))]
          simp
        have e2 : digit r (j % 3 ^ m) = digit r j := by
          conv_rhs => rw [hdec_j]
          rw [show digit m j * 3 ^ m + j % 3 ^ m = 0 * 3 ^ (m + 1) + digit m j * 3 ^ m + j % 3 ^ m by ring,
            digit_decomp_of_ne (by omega) (digit_lt m j) (Nat.mod_lt _ (by positivity))]
          simp
        rw [e1, e2, h r]
      · -- above m both remainders have digit 0
        have hle : 3 ^ m ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
        unfold digit
        rw [Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hle),
          Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hle)]
    rw [hdec_i, hdec_j, h m, hlo]

/-- Other positions are untouched by a toggle. -/
theorem digit_togIdx_of_ne {p q i : ℕ} (hpq : q ≠ p) : digit q (togIdx p i) = digit q i := by
  have hd := digit_lt p i
  have hpos : 0 < 3 ^ p := by positivity
  have hlo := Nat.mod_lt i hpos
  have hdec := decomp p i
  -- work with the decomposition around `p`
  suffices key : ∀ hi d lo : ℕ, d < 3 → lo < 3 ^ p →
      digit q (hi * 3 ^ (p + 1) + d * 3 ^ p + lo) = digit q (hi * 3 ^ (p + 1) + lo) by
    unfold togIdx
    split_ifs with h1 h2
    · conv_lhs => rw [hdec, h1]
      rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p + 3 ^ p
          = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p by ring]
      rw [key _ _ _ (by norm_num) hlo]
      conv_rhs => rw [hdec, h1]
      rw [key _ _ _ (by norm_num) hlo]
    · conv_lhs => rw [hdec, h2]
      rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p - 3 ^ p
          = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p from sub_block21]
      rw [key _ _ _ (by norm_num) hlo]
      conv_rhs => rw [hdec, h2]
      rw [key _ _ _ (by norm_num) hlo]
    · rfl
  intro hi d lo hd hlo
  exact digit_decomp_of_ne hpq hd hlo

end Bulk
end FourColor

import Mathlib.Algebra.Order.Group.Nat

/-!
# Dyck numbers

`genDyck m n` counts balanced bracket-word fragments of length `n` carrying
`m - 1` extra closing brackets, and `dyck n = genDyck 1 n` counts balanced
bracket words of length `n`.  These are the Catalan numbers in disguise —
`dyck n` is `catalan (n / 2)` for even `n` and `0` for odd `n` — but the
recurrence used here is non-standard, chosen because it makes the correctness
proof of the reducibility check's initial data straightforward.  Dyck numbers
are the only link between the initial colour tree and the initial chromogram
tree.

## References

Gonthier's `theories/proof/dyck.v`.
-/

namespace FourColor

/-- `genDyck m n`: the number of balanced bracket-word fragments of length `n`
with `m - 1` extra closing brackets. -/
def genDyck : ℕ → ℕ → ℕ
  | 1, 0 => 1
  | _, 0 => 0
  | 0, _ + 1 => 0
  | (m + 1), (n + 1) => genDyck (m + 2) n + genDyck m n

/-- The number of balanced bracket words of length `n`. -/
def dyck : ℕ → ℕ := genDyck 1

@[simp] theorem genDyck_one_zero : genDyck 1 0 = 1 := rfl

@[simp] theorem genDyck_zero_succ (n : ℕ) : genDyck 0 (n + 1) = 0 := rfl

theorem genDyck_succ_succ (m n : ℕ) :
    genDyck (m + 1) (n + 1) = genDyck (m + 2) n + genDyck m n := by
  simp [genDyck]

/-- There are no fragments when too many closing brackets are required. -/
theorem genDyck_eq_zero {m n : ℕ} (h : n + 1 < m) : genDyck m n = 0 := by
  induction n generalizing m with
  | zero =>
    match m, h with
    | 0, _ => rfl
    | (m + 2), _ => rfl
  | succ n ih =>
    match m, h with
    | (m + 1), h =>
      rw [genDyck_succ_succ]
      rw [ih (by omega), ih (by omega)]

/-- A fragment of length `m` with `m` extra closing brackets is unique: close
every bracket. -/
theorem genDyck_succ_self (m : ℕ) : genDyck (m + 1) m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [genDyck_succ_succ, ih, genDyck_eq_zero (by omega)]

theorem genDyck_pos (m n : ℕ) : 0 < genDyck (m + 1) (2 * n + m) := by
  induction n generalizing m with
  | zero =>
    have harg : 2 * 0 + m = m := by omega
    rw [harg, genDyck_succ_self]
    omega
  | succ n ih =>
    have harg : 2 * (n + 1) + m = (2 * n + (m + 1)) + 1 := by omega
    rw [harg, genDyck_succ_succ]
    have h := ih (m + 1)
    rw [show m + 1 + 1 = m + 2 from rfl] at h
    omega

/-- There is at least one balanced bracket word of each even length. -/
theorem dyck_two_mul_pos (n : ℕ) : 0 < dyck (2 * n) := by
  simpa [dyck] using genDyck_pos 0 n

end FourColor

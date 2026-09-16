import FourColor.Bulk.Masks

/-!
# The pair check

A trace certified with position `p` must, for every position `q` that could be
the other end of `p`'s chord, have one of three flips ranking strictly below it:
the chord `{p, q}` alone, every position strictly between, or both.  For one
unordered pair `{p, q}` this is one bulk computation over every trace at once:

* `pairW m p q R H` — the traces for which one of the three flips has a witness
  rank (`H`) below their own rank (`R`);
* `pairOk m p q R H choice` — every trace of `choice` that is `compat` for the
  pair lies in `pairW`.

When the two ends are far apart the walk toggles the *outside* of the chord
instead, which is cheaper; on planes invariant under swapping `c2` and `c3`
everywhere that gives the same three candidates (`pairOk_spec`).
-/

namespace FourColor
namespace Bulk

open Color
open scoped List

/-! ### Toggles commute -/

theorem digit_togIdx_self (p i : ℕ) :
    digit p (togIdx p i) = if digit p i = 1 then 2 else if digit p i = 2 then 1 else 0 := by
  have hd := digit_lt p i
  have hlo := Nat.mod_lt i (show 0 < 3 ^ p by positivity)
  have hdec := decomp p i
  unfold togIdx
  by_cases h1 : digit p i = 1
  · rw [if_pos h1, if_pos h1]
    conv_lhs => rw [hdec, h1]
    rw [show i / 3 ^ (p + 1) * 3 ^ (p + 1) + 1 * 3 ^ p + i % 3 ^ p + 3 ^ p
        = i / 3 ^ (p + 1) * 3 ^ (p + 1) + 2 * 3 ^ p + i % 3 ^ p by ring]
    exact digit_of_decomp (by norm_num) hlo
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : digit p i = 2
    · rw [if_pos h2, if_pos h2]
      conv_lhs => rw [hdec, h2]
      rw [sub_block21]
      exact digit_of_decomp (by norm_num) hlo
    · rw [if_neg h2, if_neg h2]; omega

theorem togIdx_comm (a b j : ℕ) : togIdx a (togIdx b j) = togIdx b (togIdx a j) := by
  by_cases hab : a = b
  · subst hab; rfl
  -- pick a width holding everything
  set M := max a b + j + 1 with hM
  have ha : a < M := by omega
  have hb : b < M := by omega
  have hj : j < 3 ^ M := lt_of_lt_of_le (by omega) (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  apply digits_ext (togIdx_lt ha (togIdx_lt hb hj)) (togIdx_lt hb (togIdx_lt ha hj))
  intro r
  by_cases hr : r = a
  · subst hr
    rw [digit_togIdx_self, digit_togIdx_of_ne hab, digit_togIdx_of_ne hab, digit_togIdx_self]
  by_cases hr' : r = b
  · subst hr'
    rw [digit_togIdx_of_ne (Ne.symm hab), digit_togIdx_self, digit_togIdx_self,
      digit_togIdx_of_ne (Ne.symm hab)]
  · rw [digit_togIdx_of_ne hr, digit_togIdx_of_ne hr', digit_togIdx_of_ne hr', digit_togIdx_of_ne hr]

theorem togIdxs_perm (m : ℕ) {S T : List ℕ} (h : S.Perm T) (i : ℕ) :
    togIdxs m S i = togIdxs m T i := by
  induction h generalizing i with
  | nil => rfl
  | cons x _ ih => simp [togIdxs, ih]
  | swap x y l =>
    simp only [togIdxs]
    split_ifs <;> simp [togIdx_comm]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem togIdxs_self_self {m : ℕ} {j : ℕ} (hj : j < 3 ^ m) : ∀ L : List ℕ, togIdxs m (L ++ L) j = j := by
  intro L
  induction L with
  | nil => rfl
  | cons r L ih =>
    have hp : (r :: L ++ r :: L).Perm (r :: r :: (L ++ L)) := by
      simp only [List.cons_append]
      exact List.Perm.cons r (List.perm_middle)
    rw [togIdxs_perm m hp]
    simp only [togIdxs]
    split_ifs with hr
    · rw [togIdx_togIdx hr (togIdxs_lt hj _), ih]
    · exact ih

/-! ### The arcs of a chord -/

/-- The positions strictly between `p` and `q`. -/
def inside (p q : ℕ) : List ℕ := List.range' (p + 1) (q - p - 1)

/-- The positions outside the chord `{p, q}`, up to `m`. -/
def outside (m p q : ℕ) : List ℕ := List.range' (q + 1) (m - q) ++ List.range' 0 p

theorem range_split {m p q : ℕ} (hpq : p < q) (hq : q ≤ m) :
    List.range' 0 (m + 1) =
      List.range' 0 p ++ [p] ++ inside p q ++ [q] ++ List.range' (q + 1) (m - q) := by
  unfold inside
  have e1 : List.range' 0 (m + 1) = List.range' 0 p ++ List.range' p (m + 1 - p) := by
    have := @List.range'_append_1 0 p (m + 1 - p)
    rw [Nat.zero_add, show p + (m + 1 - p) = m + 1 by omega] at this
    exact this.symm
  have e2 : List.range' p (m + 1 - p) = p :: List.range' (p + 1) (m - p) := by
    rw [show m + 1 - p = (m - p) + 1 by omega, List.range'_succ]
  have e3 : List.range' (p + 1) (m - p) =
      List.range' (p + 1) (q - p - 1) ++ List.range' q (m - q + 1) := by
    have := @List.range'_append_1 (p + 1) (q - p - 1) (m - q + 1)
    rw [show p + 1 + (q - p - 1) = q by omega, show q - p - 1 + (m - q + 1) = m - p by omega] at this
    exact this.symm
  have e4 : List.range' q (m - q + 1) = q :: List.range' (q + 1) (m - q) := List.range'_succ
  rw [e1, e2, e3, e4]
  simp

theorem outside_perm {m p q : ℕ} (hpq : p < q) (hq : q ≤ m) :
    (outside m p q ++ [p, q] ++ inside p q).Perm (List.range' 0 (m + 1)) := by
  rw [range_split hpq hq]
  unfold outside
  -- Z ++ X ++ [p, q] ++ Y ~ X ++ [p] ++ Y ++ [q] ++ Z
  set X := List.range' 0 p
  set Y := inside p q
  set Z := List.range' (q + 1) (m - q)
  calc Z ++ X ++ [p, q] ++ Y = Z ++ (X ++ [p, q] ++ Y) := by simp [List.append_assoc]
    _ ~ (X ++ [p, q] ++ Y) ++ Z := List.perm_append_comm
    _ = X ++ [p] ++ (q :: Y) ++ Z := by simp
    _ ~ X ++ [p] ++ (Y ++ [q]) ++ Z := by
        apply List.Perm.append_right
        apply List.Perm.append_left
        simpa using (List.perm_middle (l₁ := Y) (a := q) (l₂ := [])).symm
    _ = X ++ [p] ++ Y ++ [q] ++ Z := by simp [List.append_assoc]

/-! ### The pair check -/

/-- The traces for which one of the three flips along the chord `{p, q}` has
witness rank (`H`) strictly below the trace's rank (`R`). -/
def pairW (m p q : ℕ) (R H : List ℕ) : ℕ :=
  let inner := q - p - 1
  let outer := m + 1 - 2 - inner
  if inner ≤ outer then
    let A := togMany m (inside p q) H
    let C := togMany m [p, q] H
    let CI := togMany m [p, q] A
    lt m A R 0 ||| lt m C R 0 ||| lt m CI R 0
  else
    let B := togMany m (outside m p q) H
    let C := togMany m [p, q] H
    let I := togMany m [p, q] B
    lt m I R 0 ||| lt m C R 0 ||| lt m B R 0

/-- Every trace of `choice` that is `compat` for the pair has a lower-ranked flip. -/
def pairOk (m p q : ℕ) (R H : List ℕ) (choice : ℕ) : Bool :=
  (choice &&& compat m p q &&& ((2 ^ 3 ^ m - 1) ^^^ pairW m p q R H)) == 0

theorem testBit_lt0 {m : ℕ} {A B : List ℕ} (hlen : A.length = B.length) (i : ℕ) (hi : i < 3 ^ m) :
    (lt m A B 0).testBit i = decide (val A i < val B i) := by
  rw [testBit_lt m i hi A B 0 hlen]
  simp

/-- **Specification of the pair check.**  On witness planes `H` invariant under
swapping `c2` and `c3` everywhere, a trace passing the check has one of the
three candidate flips strictly below its rank. -/
theorem pairOk_spec {m p q : ℕ} (hpq : p < q) (hq : q ≤ m) {R H : List ℕ}
    (hlen : R.length = H.length)
    (hH : ∀ j, j < 3 ^ m → val H (togIdxs m (List.range' 0 (m + 1)) j) = val H j)
    {choice : ℕ} (h : pairOk m p q R H choice = true) :
    ∀ i, i < 3 ^ m → choice.testBit i = true → (compat m p q).testBit i = true →
      val H (togIdxs m [p, q] i) < val R i ∨
      val H (togIdxs m (inside p q) i) < val R i ∨
      val H (togIdxs m (p :: q :: inside p q) i) < val R i := by
  intro i hi hc hcmp
  have h0 : choice &&& compat m p q &&& ((2 ^ 3 ^ m - 1) ^^^ pairW m p q R H) = 0 := by
    simpa [pairOk] using h
  have hbit := congrArg (fun x => x.testBit i) h0
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
    hc, hcmp, hi, decide_true, Bool.true_and, Bool.true_xor, Bool.not_eq_false'] at hbit
  -- `hbit : (pairW m p q R H).testBit i = true`
  have hlenH : ∀ S, (togMany m S H).length = R.length := by intro S; simp [hlen]
  have hlenH2 : ∀ S T, (togMany m S (togMany m T H)).length = R.length := by
    intro S T; simp [hlen]
  dsimp only [pairW] at hbit
  split_ifs at hbit with hio
  · simp only [Nat.testBit_or, testBit_lt0 (hlenH _) i hi, testBit_lt0 (hlenH2 _ _) i hi,
      val_togMany _ _ _ hi, val_togMany _ _ _ (togIdxs_lt hi _), Bool.or_eq_true,
      decide_eq_true_eq] at hbit
    rcases hbit with (h1 | h1) | h1
    · right; left; exact h1
    · left; exact h1
    · right; right
      rw [← togIdxs_append] at h1
      rwa [togIdxs_perm m (show (inside p q ++ [p, q]).Perm (p :: q :: inside p q) from
        List.perm_append_comm)] at h1
  · simp only [Nat.testBit_or, testBit_lt0 (hlenH _) i hi, testBit_lt0 (hlenH2 _ _) i hi,
      val_togMany _ _ _ hi, val_togMany _ _ _ (togIdxs_lt hi _), Bool.or_eq_true,
      decide_eq_true_eq] at hbit
    -- toggling one side of a partition of the ring is toggling the other side, up to `e132`
    have hswap : ∀ A L : List ℕ, (A ++ L).Perm (List.range' 0 (m + 1)) →
        ∀ j, j < 3 ^ m → val H (togIdxs m A j) = val H (togIdxs m L j) := by
      intro A L hAL j hj
      have h1 := hH (togIdxs m L j) (togIdxs_lt hj L)
      rw [← togIdxs_append, togIdxs_perm m (hAL.symm.append_right L), List.append_assoc,
        togIdxs_append, togIdxs_self_self hj] at h1
      exact h1
    have hperm := outside_perm hpq hq
    rcases hbit with (h1 | h1) | h1
    · right; left
      rw [← togIdxs_append,
        hswap (outside m p q ++ [p, q]) (inside p q) hperm i hi] at h1
      exact h1
    · left; exact h1
    · right; right
      rw [hswap (outside m p q) ([p, q] ++ inside p q) (by simpa [List.append_assoc] using hperm)
        i hi] at h1
      exact h1

end Bulk
end FourColor

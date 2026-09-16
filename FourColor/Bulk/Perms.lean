import FourColor.Bulk.Masks
import FourColor.Bulk.Pair

/-!
# Colour permutations of traces, and the least rank in an orbit

A colour permutation acts on the digits of a trace index: since the digits `0`,
`1`, `2` stand for the colours `c1`, `c2`, `c3`, and an `EdgePerm` permutes
those three colours, every `g : EdgePerm` induces a permutation `σg g` of
`{0, 1, 2}` and hence a permutation `permIdx g m` of the indices below `3 ^ m`.
It is the index form of mapping the trace itself: `traceOf m (permIdx g m i)` is
`(traceOf m i).map g`.

On masks the same action is a fold of `permDigit` over the stored positions,
which costs a handful of `Nat` primitives however many traces are involved.

* `σg g`, `digitPerm_σg` — the digit permutation and its inverse.
* `permIdx`, `traceOf_permIdx` — the index action, and that it is the trace map.
* `permMask`, `permPlanes` — the action on one mask and on a list of bit planes.
* `minPlanes` — the lane-wise minimum of two ranks, bit-sliced.
* `minPerm` — the least rank over the six colour permutations of each trace;
  `exists_val_minPerm` names a permutation attaining it and
  `val_minPerm_permIdx` says the result is constant on each orbit.
-/

namespace FourColor
namespace Bulk

open Color EdgePerm

/-! ### Colours as digits -/

/-- The digit a colour stands for: `c1 ↦ 0`, `c2 ↦ 1`, `c3 ↦ 2`; `c0` is junk. -/
def digitOf : Color → ℕ
  | c0 => 0
  | c1 => 0
  | c2 => 1
  | c3 => 2

theorem digitOf_lt (c : Color) : digitOf c < 3 := by cases c <;> decide

theorem colourOfDigit_digitOf {c : Color} (hc : c ≠ 0) : colourOfDigit (digitOf c) = c := by
  cases c with
  | c0 => exact absurd rfl hc
  | c1 => rfl
  | c2 => rfl
  | c3 => rfl

theorem digitOf_colourOfDigit {d : ℕ} (hd : d < 3) : digitOf (colourOfDigit d) = d := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (n + 3) => omega

/-! ### The digit action of a colour permutation -/

/-- The digit action of a colour permutation: `σg g d` is the digit of the
colour `g` sends digit `d`'s colour to. -/
def σg (g : EdgePerm) (d : ℕ) : ℕ := digitOf (g (colourOfDigit d))

theorem σg_lt (g : EdgePerm) (d : ℕ) : σg g d < 3 := digitOf_lt _

/-- `σg` is the digit form of the action on colours. -/
theorem colourOfDigit_σg (g : EdgePerm) (d : ℕ) :
    colourOfDigit (σg g d) = g (colourOfDigit d) :=
  colourOfDigit_digitOf fun h => colourOfDigit_ne_zero d (apply_eq_zero.mp h)

theorem σg_σg (g h : EdgePerm) (d : ℕ) : σg g (σg h d) = σg (g * h) d := by
  show digitOf (g (colourOfDigit (σg h d))) = digitOf ((g * h) (colourOfDigit d))
  rw [colourOfDigit_σg, mul_apply]

theorem σg_one {d : ℕ} (hd : d < 3) : σg 1 d = d := by
  unfold σg
  rw [one_apply, digitOf_colourOfDigit hd]

/-- `σg g` permutes `{0, 1, 2}`, with inverse `σg g⁻¹`. -/
theorem digitPerm_σg (g : EdgePerm) : DigitPerm (σg g) (σg g⁻¹) where
  lt := fun d _ => σg_lt g d
  left_inv := fun d hd => by rw [σg_σg, inv_mul_cancel, σg_one hd]
  right_inv := fun d hd => by rw [σg_σg, mul_inv_cancel, σg_one hd]
  tau_lt := fun d _ => σg_lt _ d

/-! ### The index action -/

/-- Index of the trace `(traceOf m i).map g`: the digits below `m` of `i` sent
through `σg g`, the rest left alone. -/
def permIdx (g : EdgePerm) : ℕ → ℕ → ℕ
  | 0, i => i
  | m + 1, i => setDigit m (σg g (digit m i)) (permIdx g m i)

@[simp] theorem permIdx_zero (g : EdgePerm) (i : ℕ) : permIdx g 0 i = i := rfl

theorem permIdx_succ (g : EdgePerm) (m i : ℕ) :
    permIdx g (m + 1) i = setDigit m (σg g (digit m i)) (permIdx g m i) := rfl

/-- The stored digits are permuted. -/
theorem digit_permIdx (g : EdgePerm) {m i p : ℕ} (hp : p < m) :
    digit p (permIdx g m i) = σg g (digit p i) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [permIdx_succ]
    rcases Nat.lt_or_ge p m with h | h
    · rw [digit_setDigit_of_ne (by omega) (σg_lt _ _), ih h]
    · have : p = m := by omega
      subst this
      rw [digit_setDigit_self (σg_lt _ _)]

/-- Positions from `m` up are untouched. -/
theorem digit_permIdx_of_ge (g : EdgePerm) {m i p : ℕ} (hp : m ≤ p) :
    digit p (permIdx g m i) = digit p i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [permIdx_succ, digit_setDigit_of_ne (by omega) (σg_lt _ _), ih (by omega)]

theorem permIdx_lt_of_le (g : EdgePerm) {m n i : ℕ} (hmn : m ≤ n) (hi : i < 3 ^ n) :
    permIdx g m i < 3 ^ n := by
  induction m with
  | zero => exact hi
  | succ m ih => exact setDigit_lt (by omega) (σg_lt _ _) (ih (by omega))

theorem permIdx_lt (g : EdgePerm) {m i : ℕ} (hi : i < 3 ^ m) : permIdx g m i < 3 ^ m :=
  permIdx_lt_of_le g le_rfl hi

/-- The permuted index carries the permuted trace. -/
theorem traceOf_permIdx (g : EdgePerm) (m i : ℕ) :
    traceOf m (permIdx g m i) = (traceOf m i).map g := by
  have hpart : partialOf m (permIdx g m i) = (partialOf m i).map g := by
    unfold partialOf
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    rw [List.mem_range] at hp
    rw [digit_permIdx g hp, colourOfDigit_σg]
    rfl
  rw [traceOf, hpart, map_completeTrace, traceOf]

theorem permIdx_permIdx (g h : EdgePerm) {m i : ℕ} (hi : i < 3 ^ m) :
    permIdx g m (permIdx h m i) = permIdx (g * h) m i := by
  refine digits_ext (permIdx_lt g (permIdx_lt h hi)) (permIdx_lt _ hi) fun r => ?_
  rcases Nat.lt_or_ge r m with hr | hr
  · rw [digit_permIdx g hr, digit_permIdx h hr, digit_permIdx _ hr, σg_σg]
  · rw [digit_permIdx_of_ge g hr, digit_permIdx_of_ge h hr, digit_permIdx_of_ge _ hr]

theorem permIdx_one {m i : ℕ} (hi : i < 3 ^ m) : permIdx 1 m i = i := by
  refine digits_ext (permIdx_lt _ hi) hi fun r => ?_
  rcases Nat.lt_or_ge r m with hr | hr
  · rw [digit_permIdx _ hr, σg_one (digit_lt r i)]
  · rw [digit_permIdx_of_ge _ hr]

/-- Replacing a digit commutes with permuting the lower digits. -/
theorem permIdx_setDigit (g : EdgePerm) {n k v i : ℕ} (hk : k < n) (hv : v < 3)
    (hi : i < 3 ^ n) :
    permIdx g k (setDigit k v i) = setDigit k v (permIdx g k i) := by
  refine digits_ext (permIdx_lt_of_le g (by omega) (setDigit_lt hk hv hi))
    (setDigit_lt hk hv (permIdx_lt_of_le g (by omega) hi)) fun r => ?_
  rcases Nat.lt_or_ge r k with hr | hr
  · rw [digit_permIdx g hr, digit_setDigit_of_ne (by omega) hv,
      digit_setDigit_of_ne (by omega) hv, digit_permIdx g hr]
  · rcases Nat.eq_or_lt_of_le hr with hr' | hr'
    · subst hr'
      rw [digit_permIdx_of_ge g le_rfl, digit_setDigit_self hv, digit_setDigit_self hv]
    · rw [digit_permIdx_of_ge g hr, digit_setDigit_of_ne (by omega) hv,
        digit_setDigit_of_ne (by omega) hv, digit_permIdx_of_ge g (by omega)]

/-! ### The action on masks -/

/-- `permMaskAux g m k M` permutes digits `0, …, k - 1` of `M`, a mask of traces
below `3 ^ m`. -/
def permMaskAux (g : EdgePerm) (m : ℕ) : ℕ → ℕ → ℕ
  | 0, M => M
  | k + 1, M => permDigit m k (σg g) (permMaskAux g m k M)

/-- The mask `M` pushed forward along `g`: bit `i` is bit `permIdx g⁻¹ m i`. -/
def permMask (g : EdgePerm) (m M : ℕ) : ℕ := permMaskAux g m m M

theorem testBit_permMaskAux (g : EdgePerm) {m : ℕ} :
    ∀ (k : ℕ), k ≤ m → ∀ (M i : ℕ), i < 3 ^ m →
      (permMaskAux g m k M).testBit i = M.testBit (permIdx g⁻¹ k i) := by
  intro k
  induction k with
  | zero => intro _ M i _; rfl
  | succ k ih =>
    intro hk M i hi
    rw [permMaskAux, testBit_permDigit (by omega) (digitPerm_σg g) _ _ hi,
      ih (by omega) _ _ (setDigit_lt (by omega) (σg_lt _ _) hi),
      permIdx_setDigit g⁻¹ (n := m) (by omega) (σg_lt _ _) hi, permIdx_succ]

theorem testBit_permMask (g : EdgePerm) {m : ℕ} (M i : ℕ) (hi : i < 3 ^ m) :
    (permMask g m M).testBit i = M.testBit (permIdx g⁻¹ m i) :=
  testBit_permMaskAux g m le_rfl M i hi

/-- `permMask` on every plane of a rank. -/
def permPlanes (g : EdgePerm) (m : ℕ) (L : List ℕ) : List ℕ := L.map (permMask g m)

@[simp] theorem length_permPlanes (g : EdgePerm) (m : ℕ) (L : List ℕ) :
    (permPlanes g m L).length = L.length := by simp [permPlanes]

theorem val_permPlanes (g : EdgePerm) {m : ℕ} (L : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    val (permPlanes g m L) i = val L (permIdx g⁻¹ m i) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    unfold permPlanes at ih ⊢
    rw [List.map_cons, val, val, testBit_permMask g a i hi, ih]

/-! ### Lane-wise minimum -/

/-- Lane-wise minimum of two ranks: where `A < B` take `A`'s bits, else `B`'s. -/
def minPlanes (m : ℕ) (A B : List ℕ) : List ℕ :=
  let c := lt m A B 0
  List.zipWith (fun a b => (c &&& a) ||| (((2 ^ 3 ^ m - 1) ^^^ c) &&& b)) A B

theorem minPlanes_eq (m : ℕ) (A B : List ℕ) :
    minPlanes m A B =
      List.zipWith
        (fun a b => (lt m A B 0 &&& a) ||| (((2 ^ 3 ^ m - 1) ^^^ lt m A B 0) &&& b)) A B := rfl

@[simp] theorem length_minPlanes (m : ℕ) (A B : List ℕ) :
    (minPlanes m A B).length = min A.length B.length := by
  rw [minPlanes_eq]; simp

theorem length_minPlanes_of_length {m : ℕ} {A B : List ℕ} (hlen : A.length = B.length) :
    (minPlanes m A B).length = A.length := by simp [hlen]

/-- Selecting between two ranks by a mask, bit by bit. -/
theorem val_zipWith_select {m : ℕ} (c : ℕ) {i : ℕ} (hi : i < 3 ^ m) :
    ∀ (A B : List ℕ), A.length = B.length →
      val (List.zipWith (fun a b => (c &&& a) ||| (((2 ^ 3 ^ m - 1) ^^^ c) &&& b)) A B) i
        = if c.testBit i then val A i else val B i := by
  intro A
  induction A with
  | nil =>
    intro B hlen
    cases B with
    | nil => simp [val]
    | cons b bs => simp at hlen
  | cons a as ih =>
    intro B hlen
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hbit : ((c &&& a) ||| (((2 ^ 3 ^ m - 1) ^^^ c) &&& b)).testBit i
          = if c.testBit i then a.testBit i else b.testBit i := by
        rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor,
          Nat.testBit_two_pow_sub_one]
        simp only [hi, decide_true, Bool.true_xor]
        cases c.testBit i <;> simp
      rw [List.zipWith_cons_cons, val, ih bs hlen, hbit]
      cases c.testBit i <;> simp [val]

theorem val_minPlanes {m : ℕ} {A B : List ℕ} (hlen : A.length = B.length) (i : ℕ)
    (hi : i < 3 ^ m) : val (minPlanes m A B) i = min (val A i) (val B i) := by
  rw [minPlanes_eq, val_zipWith_select _ hi A B hlen, testBit_lt m i hi A B 0 hlen]
  simp only [Nat.zero_testBit, Bool.false_eq_true, and_false, or_false]
  by_cases h : val A i < val B i
  · rw [if_pos (by simpa using h), Nat.min_def, if_pos (by omega)]
  · rw [if_neg (by simpa using h), Nat.min_def]
    by_cases h' : val A i ≤ val B i
    · rw [if_pos h']; omega
    · rw [if_neg h']

/-! ### The minimum over all six colour permutations -/

/-- The six colour permutations. -/
def allPerms : List EdgePerm := [.e123, .e132, .e213, .e231, .e312, .e321]

theorem mem_allPerms (g : EdgePerm) : g ∈ allPerms := by cases g <;> decide

/-- The least rank among the colour permutations of each trace. -/
def minPerm (m : ℕ) (R : List ℕ) : List ℕ :=
  allPerms.foldr (fun g acc => minPlanes m (permPlanes g⁻¹ m R) acc) R

theorem length_foldr_minPlanes (m : ℕ) (R : List ℕ) : ∀ L : List EdgePerm,
    (L.foldr (fun g acc => minPlanes m (permPlanes g⁻¹ m R) acc) R).length = R.length := by
  intro L
  induction L with
  | nil => rfl
  | cons g L ih => rw [List.foldr_cons, length_minPlanes, length_permPlanes, ih, Nat.min_self]

@[simp] theorem length_minPerm (m : ℕ) (R : List ℕ) : (minPerm m R).length = R.length :=
  length_foldr_minPlanes m R allPerms

theorem val_foldr_minPlanes {m : ℕ} (R : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    ∀ L : List EdgePerm,
      val (L.foldr (fun g acc => minPlanes m (permPlanes g⁻¹ m R) acc) R) i
        = (L.map fun g => val R (permIdx g m i)).foldr min (val R i) := by
  intro L
  induction L with
  | nil => rfl
  | cons g L ih =>
    have hlen : (permPlanes g⁻¹ m R).length
        = (L.foldr (fun g acc => minPlanes m (permPlanes g⁻¹ m R) acc) R).length := by
      rw [length_permPlanes, length_foldr_minPlanes]
    rw [List.foldr_cons, val_minPlanes hlen i hi, val_permPlanes _ _ _ hi, inv_inv, ih,
      List.map_cons, List.foldr_cons]

theorem val_minPerm {m : ℕ} (R : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    val (minPerm m R) i = (allPerms.map fun g => val R (permIdx g m i)).foldr min (val R i) :=
  val_foldr_minPlanes R i hi allPerms

theorem foldr_min_le : ∀ (l : List ℕ) (b : ℕ) {x : ℕ}, x ∈ l → l.foldr min b ≤ x := by
  intro l
  induction l with
  | nil => intro b x hx; simp at hx
  | cons a l ih =>
    intro b x hx
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.min_le_left _ _
    · exact le_trans (Nat.min_le_right _ _) (ih b hx)

theorem foldr_min_mem : ∀ (l : List ℕ) (b : ℕ), l.foldr min b = b ∨ l.foldr min b ∈ l := by
  intro l
  induction l with
  | nil => intro b; exact Or.inl rfl
  | cons a l ih =>
    intro b
    rw [List.foldr_cons]
    rcases Nat.le_total a (l.foldr min b) with hab | hab
    · rw [Nat.min_eq_left hab]; exact Or.inr (List.mem_cons_self ..)
    · rw [Nat.min_eq_right hab]
      rcases ih b with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem val_minPerm_le (g : EdgePerm) {m : ℕ} (R : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    val (minPerm m R) i ≤ val R (permIdx g m i) := by
  rw [val_minPerm R i hi]
  exact foldr_min_le _ _ (List.mem_map_of_mem (mem_allPerms g))

theorem exists_val_minPerm {m : ℕ} (R : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    ∃ g : EdgePerm, val (minPerm m R) i = val R (permIdx g m i) := by
  rw [val_minPerm R i hi]
  rcases foldr_min_mem (allPerms.map fun g => val R (permIdx g m i)) (val R i) with h | h
  · exact ⟨1, by rw [h, permIdx_one hi]⟩
  · obtain ⟨g, -, hg⟩ := List.mem_map.mp h
    exact ⟨g, hg.symm⟩

/-- The minimum is constant on each orbit of the colour permutations. -/
theorem val_minPerm_permIdx (g : EdgePerm) {m : ℕ} (R : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    val (minPerm m R) i = val (minPerm m R) (permIdx g m i) := by
  have hj : permIdx g m i < 3 ^ m := permIdx_lt g hi
  refine le_antisymm ?_ ?_
  · obtain ⟨h, hh⟩ := exists_val_minPerm R _ hj
    rw [hh, permIdx_permIdx h g hi]
    exact val_minPerm_le (h * g) R i hi
  · obtain ⟨h, hh⟩ := exists_val_minPerm R i hi
    have hback : permIdx g⁻¹ m (permIdx g m i) = i := by
      rw [permIdx_permIdx g⁻¹ g hi, inv_mul_cancel, permIdx_one hi]
    have key : permIdx (h * g⁻¹) m (permIdx g m i) = permIdx h m i := by
      rw [← permIdx_permIdx h g⁻¹ hj, hback]
    rw [hh, ← key]
    exact val_minPerm_le (h * g⁻¹) R _ hj

/-! ### Toggling every position -/

/-- The digit swap a toggle performs: `1 ↔ 2`, and `0` fixed. -/
def togDigit (d : ℕ) : ℕ := if d = 1 then 2 else if d = 2 then 1 else 0

theorem σg_e132 {d : ℕ} (hd : d < 3) : σg EdgePerm.e132 d = togDigit d := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (n + 3) => omega

theorem digit_togIdxs_range' (m i : ℕ) : ∀ (n s r : ℕ),
    digit r (togIdxs m (List.range' s n) i)
      = if s ≤ r ∧ r < s + n ∧ r < m then togDigit (digit r i) else digit r i := by
  intro n
  induction n with
  | zero => intro s r; rw [if_neg (by omega)]; rfl
  | succ n ih =>
    intro s r
    rw [show List.range' s (n + 1) = s :: List.range' (s + 1) n from rfl, togIdxs]
    by_cases hs : s < m
    · rw [if_pos hs]
      by_cases hr : r = s
      · subst hr
        have hin : digit r (togIdxs m (List.range' (r + 1) n) i) = digit r i := by
          rw [ih (r + 1) r, if_neg (by omega)]
        have hL : digit r (togIdx r (togIdxs m (List.range' (r + 1) n) i))
            = togDigit (digit r i) := by rw [digit_togIdx_self, hin]; rfl
        rw [hL, if_pos (by omega)]
      · rw [digit_togIdx_of_ne hr, ih (s + 1) r]
        have hiff : (s + 1 ≤ r ∧ r < s + 1 + n ∧ r < m)
            = (s ≤ r ∧ r < s + (n + 1) ∧ r < m) := by
          apply propext
          constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩)
        simp only [hiff]
    · rw [if_neg hs, ih (s + 1) r, if_neg (by omega), if_neg (by omega)]

/-- Toggling `c2`/`c3` at every position is the colour permutation `e132`. -/
theorem togIdxs_range'_eq_permIdx {m i : ℕ} (hi : i < 3 ^ m) :
    togIdxs m (List.range' 0 (m + 1)) i = permIdx EdgePerm.e132 m i := by
  refine digits_ext (togIdxs_lt hi _) (permIdx_lt _ hi) fun r => ?_
  rw [digit_togIdxs_range' m i (m + 1) 0 r]
  by_cases hr : r < m
  · rw [if_pos (by omega), digit_permIdx _ hr, σg_e132 (digit_lt r i)]
  · rw [if_neg (by omega), digit_permIdx_of_ge _ (by omega)]

/-- The minimum is invariant under toggling `c2`/`c3` at every position. -/
theorem val_minPerm_togAll {m : ℕ} (R : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    val (minPerm m R) (togIdxs m (List.range' 0 (m + 1)) i) = val (minPerm m R) i := by
  rw [togIdxs_range'_eq_permIdx hi, ← val_minPerm_permIdx EdgePerm.e132 R i hi]

end Bulk
end FourColor

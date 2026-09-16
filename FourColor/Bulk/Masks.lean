import FourColor.Bulk.Move

/-!
# The masks the pair check is built from

* `xacc m p` — the traces sorted by the sum of their first `p` colours, so the
  colour at the completing position `m` (the sum of all `m` digits) is a mask
  like any other.
* `nonC1 m p` — the traces whose colour at position `p` is `c2` or `c3`, for
  `p ≤ m`.
* `compat m p q` — the traces for which positions `p < q` could be the two ends
  of one Kempe chord: both non-`c1`, with an even number of non-`c1` positions
  strictly between.
* `val`, `lt` — ranks stored as bit planes, and their comparison, bit-sliced
  across all traces at once.
* `togMany`, `togIdxs` — toggling `c2`/`c3` at a list of positions, on masks
  and on indices.
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Colour sums -/

/-- The traces sorted by the sum of their first `p` colours: the components are
the traces whose partial sum is `0`, `c1`, `c2`, `c3` respectively. -/
def xacc (m : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (2 ^ 3 ^ m - 1, 0, 0, 0)
  | p + 1 =>
    let x := xacc m p
    let s0 := sel m p 0
    let s1 := sel m p 1
    let s2 := sel m p 2
    ((x.2.1 &&& s0) ||| (x.2.2.1 &&& s1) ||| (x.2.2.2 &&& s2),
     (x.1 &&& s0) ||| (x.2.2.2 &&& s1) ||| (x.2.2.1 &&& s2),
     (x.2.2.2 &&& s0) ||| (x.1 &&& s1) ||| (x.2.1 &&& s2),
     (x.2.2.1 &&& s0) ||| (x.2.1 &&& s1) ||| (x.1 &&& s2))

/-- The component of `xacc` for a colour. -/
def xaccAt (m p : ℕ) : Color → ℕ
  | c0 => (xacc m p).1
  | c1 => (xacc m p).2.1
  | c2 => (xacc m p).2.2.1
  | c3 => (xacc m p).2.2.2

theorem partialOf_succ (p i : ℕ) :
    partialOf (p + 1) i = partialOf p i ++ [colourOfDigit (digit p i)] := by
  simp [partialOf, List.range_succ]

theorem testBit_xaccAt {m p : ℕ} (hp : p ≤ m) (c : Color) (i : ℕ) :
    (xaccAt m p c).testBit i = decide (i < 3 ^ m ∧ (partialOf p i).sum = c) := by
  induction p generalizing c with
  | zero =>
    cases c <;> simp [xaccAt, xacc, partialOf, Nat.testBit_two_pow_sub_one]
  | succ p ih =>
    have hp' : p < m := hp
    have ih' := ih (Nat.le_of_lt hp')
    rw [partialOf_succ, List.sum_append, List.sum_singleton]
    have hd := digit_lt p i
    have e0 := testBit_sel hp' 0 (by norm_num) i
    have e1 := testBit_sel hp' 1 (by norm_num) i
    have e2 := testBit_sel hp' 2 (by norm_num) i
    have g0 := ih' c0
    have g1 := ih' c1
    have g2 := ih' c2
    have g3 := ih' c3
    simp only [xaccAt] at g0 g1 g2 g3
    by_cases hi : i < 3 ^ m
    · simp only [hi, true_and, decide_true] at e0 e1 e2 g0 g1 g2 g3 ⊢
      rcases (show digit p i = 0 ∨ digit p i = 1 ∨ digit p i = 2 by omega) with h | h | h <;>
        cases c <;>
        simp only [xaccAt, xacc, Nat.testBit_or, Nat.testBit_and, e0, e1, e2, g0, g1, g2, g3, h,
          colourOfDigit] <;>
        generalize (partialOf p i).sum = s <;> cases s <;> decide
    · cases c <;> simp [xaccAt, xacc, e0, e1, e2, g0, g1, g2, g3, hi]

/-! ### Non-`c1` positions -/

/-- The traces whose colour at position `p ≤ m` is `c2` or `c3`. -/
def nonC1 (m p : ℕ) : ℕ :=
  if p = m then xaccAt m m c2 ||| xaccAt m m c3 else sel m p 1 ||| sel m p 2

theorem getD_traceOf_lt {m i p : ℕ} (hp : p < m) :
    (traceOf m i).getD p 0 = colourOfDigit (digit p i) := by
  have hlen : p < (partialOf m i).length := by simpa using hp
  rw [traceOf, completeTrace, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
  simp [partialOf, hp]

theorem getD_traceOf_last (m i : ℕ) : (traceOf m i).getD m 0 = (partialOf m i).sum := by
  rw [traceOf, completeTrace, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

theorem getD_traceOf_ge {m i p : ℕ} (hp : m < p) : (traceOf m i).getD p 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by simp; omega)]
  rfl

theorem testBit_nonC1 {m p : ℕ} (hp : p ≤ m) (i : ℕ) :
    (nonC1 m p).testBit i =
      decide (i < 3 ^ m ∧ ((traceOf m i).getD p 0 = c2 ∨ (traceOf m i).getD p 0 = c3)) := by
  unfold nonC1
  split_ifs with h
  · rw [h, Nat.testBit_or, testBit_xaccAt le_rfl, testBit_xaccAt le_rfl, getD_traceOf_last]
    by_cases hi : i < 3 ^ m <;> simp [hi]
  · have hp' : p < m := lt_of_le_of_ne hp h
    rw [Nat.testBit_or, testBit_sel hp' 1 (by norm_num), testBit_sel hp' 2 (by norm_num),
      getD_traceOf_lt hp']
    have hd := digit_lt p i
    by_cases hi : i < 3 ^ m
    · rcases (show digit p i = 0 ∨ digit p i = 1 ∨ digit p i = 2 by omega) with h | h | h <;>
        simp [hi, h, colourOfDigit]
    · simp [hi]

/-! ### Chord compatibility -/

/-- The xor of `nonC1` over positions `a, …, b - 1`: the parity of the number of
non-`c1` positions in that range. -/
def xorRange (m a b : ℕ) : ℕ := (List.range' a (b - a)).foldr (fun r acc => nonC1 m r ^^^ acc) 0

/-- Positions `p < q ≤ m` can be the ends of one chord of the trace. -/
def compat (m p q : ℕ) : ℕ :=
  nonC1 m p &&& nonC1 m q &&& ((2 ^ 3 ^ m - 1) ^^^ xorRange m (p + 1) q)

/-- The non-`c1` positions of trace `i` in a range, as the pair check counts them. -/
def nonC1Count (m i a b : ℕ) : ℕ :=
  ((List.range' a (b - a)).filter fun r =>
    (traceOf m i).getD r 0 = c2 ∨ (traceOf m i).getD r 0 = c3).length

theorem parity_succ (L : ℕ) : decide ((L + 1) % 2 = 1) = !decide (L % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one L with h | h <;> simp [Nat.add_mod, h]

theorem parity_not (L : ℕ) : (!decide (L % 2 = 1)) = decide (L % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one L with h | h <;> simp [h]

theorem testBit_xorRange {m a b : ℕ} (hb : b ≤ m) (i : ℕ) (hi : i < 3 ^ m) :
    (xorRange m a b).testBit i = decide (nonC1Count m i a b % 2 = 1) := by
  unfold xorRange nonC1Count
  -- induct over the range list, which stays inside `[a, b) ⊆ [0, m]`
  suffices key : ∀ (l : List ℕ), (∀ r ∈ l, r ≤ m) →
      (l.foldr (fun r acc => nonC1 m r ^^^ acc) 0).testBit i =
        decide ((l.filter fun r => (traceOf m i).getD r 0 = c2 ∨ (traceOf m i).getD r 0 = c3).length
          % 2 = 1) by
    apply key
    intro r hr
    rw [List.mem_range'] at hr
    omega
  intro l
  induction l with
  | nil => simp
  | cons r l ih =>
    intro hl
    rw [List.foldr_cons, Nat.testBit_xor, testBit_nonC1 (hl r (List.mem_cons_self ..)) i,
      ih (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))]
    simp only [hi, true_and]
    by_cases hr : (traceOf m i).getD r 0 = c2 ∨ (traceOf m i).getD r 0 = c3
    · simp only [List.filter_cons, decide_eq_true hr, ↓reduceIte, List.length_cons, Bool.true_xor,
        parity_succ]
    · simp only [List.filter_cons, decide_eq_false hr, Bool.false_eq_true, ↓reduceIte, Bool.false_xor]

theorem testBit_compat {m p q : ℕ} (hpq : p < q) (hq : q ≤ m) (i : ℕ) :
    (compat m p q).testBit i =
      decide (i < 3 ^ m ∧
        ((traceOf m i).getD p 0 = c2 ∨ (traceOf m i).getD p 0 = c3) ∧
        ((traceOf m i).getD q 0 = c2 ∨ (traceOf m i).getD q 0 = c3) ∧
        nonC1Count m i (p + 1) q % 2 = 0) := by
  unfold compat
  by_cases hi : i < 3 ^ m
  · rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
      testBit_nonC1 (by omega) i, testBit_nonC1 hq i, testBit_xorRange hq i hi]
    simp only [hi, true_and, decide_true, Bool.true_xor, parity_not]
    by_cases h1 : (traceOf m i).getD p 0 = c2 ∨ (traceOf m i).getD p 0 = c3 <;>
      by_cases h2 : (traceOf m i).getD q 0 = c2 ∨ (traceOf m i).getD q 0 = c3 <;>
      simp [h1, h2, Bool.and_assoc]
  · rw [Nat.testBit_and, Nat.testBit_and, testBit_nonC1 (by omega) i]
    simp [hi]

/-! ### Ranks as bit planes -/

/-- The number whose binary digits are the bits `i` of the planes, least
significant plane first. -/
def val : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, i => (if a.testBit i then 1 else 0) + 2 * val as i

/-- `lt A B acc`: bit `i` is set when the rank of trace `i` in `A` is below its
rank in `B`, with `acc` carrying the comparison of the planes already folded. -/
def lt (m : ℕ) : List ℕ → List ℕ → ℕ → ℕ
  | a :: as, b :: bs, acc =>
    lt m as bs ((((2 ^ 3 ^ m - 1) ^^^ a) &&& b) ||| (((2 ^ 3 ^ m - 1) ^^^ (a ^^^ b)) &&& acc))
  | _, _, acc => acc

theorem testBit_lt (m : ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    ∀ (A B : List ℕ) (acc : ℕ), A.length = B.length →
      (lt m A B acc).testBit i =
        decide (val A i < val B i ∨ (val A i = val B i ∧ acc.testBit i = true)) := by
  intro A
  induction A with
  | nil =>
    intro B acc hlen
    cases B with
    | nil => simp [lt, val]
    | cons b bs => simp at hlen
  | cons a as ih =>
    intro B acc hlen
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [lt, ih bs _ hlen]
      simp only [val, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
        Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_xor, decide_eq_decide]
      rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (b.testBit i) with hb | hb <;>
      rcases Bool.eq_false_or_eq_true (acc.testBit i) with hacc | hacc <;>
      simp only [ha, hb, hacc, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
        Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or, Bool.and_true, Bool.and_false,
        Bool.true_xor, Bool.false_xor, ↓reduceIte, and_true, and_false, or_false, or_true,
        Bool.true_eq_false, Bool.false_eq_true, Bool.not_true, Bool.not_false] <;>
      (try (apply decide_eq_decide.mpr; constructor <;> intro h <;> omega))

/-! ### Toggling several positions -/

/-- Toggle position `p` when it is a stored digit; the completing position `m`
follows the digits and needs no change. -/
def togP (m p M : ℕ) : ℕ := if p < m then tog m p M else M

/-- Toggle `c2`/`c3` at each position of `S`, on one mask. -/
def togFun (m : ℕ) (S : List ℕ) (a : ℕ) : ℕ := S.foldl (fun a r => togP m r a) a

/-- Toggle `c2`/`c3` at each position of `S`, on every plane of `L`. -/
def togMany (m : ℕ) (S : List ℕ) (L : List ℕ) : List ℕ := L.map (togFun m S)

/-- The index map of `togFun`: `togIdx` at each stored position of `S`, applied
from the last position of `S` to the first. -/
def togIdxs (m : ℕ) : List ℕ → ℕ → ℕ
  | [], i => i
  | r :: S, i => if r < m then togIdx r (togIdxs m S i) else togIdxs m S i

theorem togIdxs_lt {m : ℕ} {i : ℕ} (hi : i < 3 ^ m) : ∀ S : List ℕ, togIdxs m S i < 3 ^ m := by
  intro S
  induction S with
  | nil => simpa [togIdxs]
  | cons r S ih =>
    unfold togIdxs
    split_ifs with hr
    · exact togIdx_lt hr ih
    · exact ih

theorem togIdxs_append (m : ℕ) (S T : List ℕ) (i : ℕ) :
    togIdxs m (S ++ T) i = togIdxs m S (togIdxs m T i) := by
  induction S with
  | nil => rfl
  | cons r S ih => simp [togIdxs, ih]

theorem testBit_togP {m p : ℕ} (M i : ℕ) (hi : i < 3 ^ m) :
    (togP m p M).testBit i = M.testBit (if p < m then togIdx p i else i) := by
  unfold togP
  split_ifs with hp
  · exact testBit_tog hp M i hi
  · rfl

theorem testBit_togFun {m : ℕ} (i : ℕ) (hi : i < 3 ^ m) :
    ∀ (S : List ℕ) (a : ℕ), (togFun m S a).testBit i = a.testBit (togIdxs m S i) := by
  intro S
  induction S with
  | nil => intro a; rfl
  | cons r S ih =>
    intro a
    unfold togFun
    rw [List.foldl_cons]
    have := ih (togP m r a)
    unfold togFun at this
    rw [this, testBit_togP _ _ (togIdxs_lt hi S)]
    rfl

theorem val_togMany {m : ℕ} (S : List ℕ) (L : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    val (togMany m S L) i = val L (togIdxs m S i) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    unfold togMany at ih ⊢
    simp [val, testBit_togFun i hi, ih]

@[simp] theorem length_togMany (m : ℕ) (S L : List ℕ) : (togMany m S L).length = L.length := by
  simp [togMany]

end Bulk
end FourColor

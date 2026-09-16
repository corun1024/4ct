import FourColor.Bulk.Small
import FourColor.MaskChord

/-!
# The bulk indices of a small universe, packed into lanes

The residual walk lives in a small universe of traces given by colour masks;
the bulk certificate lives in the space of all `3^m` traces.  Bridging the
two means knowing, for a trace of the small universe, its bulk index.
Computed one trace at a time from the colour masks that costs the kernel a
list walk per trace — far too slow for a universe of two hundred thousand.

Here the whole table is built with a few hundred wide operations instead.
`spread` moves bit `i` of a plane to position `32 * i` by `log₂` doubling
steps, so the table `packIdx` — the sum over positions `p` of
`3^p * (spread lo_p + 2 * spread hi_p)` — holds the bulk index of trace `j` in
its `j`-th 32-bit lane, and reading a lane (`lane`) is a shift and a mask.

## Main results

* `testBit_spread` — what `spread` does, bit by bit.
* `lane_packIdx` — **lane `j` of the table is `bigOf ms m j`.**
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Bits of a sum with a shifted part -/

/-- `(a + c * 2^k).testBit q`: the low `k` bits come from `a`, the rest from `c`. -/
theorem testBit_add_mul_pow {a : ℕ} (c k q : ℕ) (ha : a < 2 ^ k) :
    (a + c * 2 ^ k).testBit q = if q < k then a.testBit q else c.testBit (q - k) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  split
  · next h =>
    have hk : 2 ^ k = 2 ^ q * 2 ^ (k - q) := by rw [← Nat.pow_add]; congr 1; omega
    have hkq : 2 ^ (k - q) = 2 * 2 ^ (k - q - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    rw [show a + c * 2 ^ k = a + (c * 2 ^ (k - q)) * 2 ^ q by rw [hk]; ring,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos q), hkq,
      show a / 2 ^ q + c * (2 * 2 ^ (k - q - 1)) = a / 2 ^ q + (c * 2 ^ (k - q - 1)) * 2 by ring,
      Nat.add_mul_mod_self_right]
  · next h =>
    have hq : 2 ^ q = 2 ^ k * 2 ^ (q - k) := by rw [← Nat.pow_add]; congr 1; omega
    rw [hq, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
      Nat.div_eq_of_lt ha, Nat.zero_add, Nat.testBit_eq_decide_div_mod_eq]

/-! ### Packed lanes -/

/-- `v 0 + v 1 * 2^32 + ... + v (n-1) * 2^(32 (n-1))`: `n` lanes of 32 bits. -/
def packedF (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packedF v n + v n * 2 ^ (32 * n)

theorem packedF_lt (v : ℕ → ℕ) (hv : ∀ k, v k < 2 ^ 32) : ∀ n, packedF v n < 2 ^ (32 * n)
  | 0 => by simp [packedF]
  | n + 1 => by
    simp only [packedF]
    have h1 := packedF_lt v hv n
    have h2 := hv n
    have h3 : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
      rw [show 32 * (n + 1) = 32 * n + 32 by ring, Nat.pow_add]
    rw [h3]
    nlinarith

theorem testBit_packedF (v : ℕ → ℕ) (hv : ∀ k, v k < 2 ^ 32) :
    ∀ n q, (packedF v n).testBit q = (decide (q / 32 < n) && (v (q / 32)).testBit (q % 32))
  | 0, q => by simp [packedF]
  | n + 1, q => by
    simp only [packedF]
    rw [testBit_add_mul_pow _ _ _ (packedF_lt v hv n)]
    split
    · next h =>
      rw [testBit_packedF v hv n q]
      have h1 : q / 32 < n := by omega
      simp [h1, show q / 32 < n + 1 by omega]
    · next h =>
      by_cases hq : q < 32 * (n + 1)
      · have hqn : q / 32 = n := by omega
        have hqm : q - 32 * n = q % 32 := by omega
        rw [hqm, hqn]; simp
      · have hb : (v n).testBit (q - 32 * n) = false :=
          Nat.testBit_lt_two_pow
            (lt_of_lt_of_le (hv n) (Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [hb]
        simp [show ¬ (q / 32 < n + 1) by omega]

/-- Lane `j` of a packed number. -/
def lane (T j : ℕ) : ℕ := (T >>> (32 * j)) &&& (2 ^ 32 - 1)

theorem lane_packedF (v : ℕ → ℕ) (hv : ∀ k, v k < 2 ^ 32) (n j : ℕ) (hj : j < n) :
    lane (packedF v n) j = v j := by
  apply Nat.eq_of_testBit_eq
  intro q
  unfold lane
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, testBit_packedF v hv]
  by_cases hq : q < 32
  · have h1 : (32 * j + q) / 32 = j := by omega
    have h2 : (32 * j + q) % 32 = q := by omega
    simp [h1, h2, hj, hq]
  · have hb : (v j).testBit q = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (hv j) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hq, hb]

theorem packedF_add (v w : ℕ → ℕ) :
    ∀ n, packedF (fun k => v k + w k) n = packedF v n + packedF w n
  | 0 => rfl
  | n + 1 => by simp only [packedF, packedF_add v w n]; ring

theorem packedF_mul (c : ℕ) (v : ℕ → ℕ) : ∀ n, packedF (fun k => c * v k) n = c * packedF v n
  | 0 => by simp [packedF]
  | n + 1 => by simp only [packedF, packedF_mul c v n]; ring

theorem packedF_zero : ∀ n, packedF (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp [packedF, packedF_zero n]

/-! ### Spreading a plane into lanes -/

/-- The positions below `32 * 2^L` whose bit `b` is set. -/
def bitMaskB (b L : ℕ) : ℕ := rep ((2 ^ 2 ^ b - 1) <<< 2 ^ b) (2 ^ (b + 1)) 64 (2 ^ (L + 4 - b))

theorem testBit_bitMaskB {b L : ℕ} (hb : b ≤ L) (hL : L < 40) (q : ℕ) :
    (bitMaskB b L).testBit q = (decide (q < 32 * 2 ^ L) && q.testBit b) := by
  unfold bitMaskB
  have hw : 0 < 2 ^ 2 ^ b := Nat.two_pow_pos _
  have hx : (2 ^ 2 ^ b - 1) <<< 2 ^ b < 2 ^ 2 ^ (b + 1) := by
    rw [Nat.shiftLeft_eq, Nat.pow_succ, Nat.pow_mul]
    have h1 : 2 ^ 2 ^ b - 1 < 2 ^ 2 ^ b := Nat.sub_lt hw Nat.one_pos
    calc (2 ^ 2 ^ b - 1) * 2 ^ 2 ^ b < 2 ^ 2 ^ b * 2 ^ 2 ^ b :=
          Nat.mul_lt_mul_of_pos_right h1 hw
      _ = (2 ^ 2 ^ b) ^ 2 := by ring
  have hk : 2 ^ (L + 4 - b) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [testBit_rep _ _ hx 64 _ q hk]
  have hlen : 2 ^ (b + 1) * 2 ^ (L + 4 - b) = 32 * 2 ^ L := by
    rw [← Nat.pow_add, show b + 1 + (L + 4 - b) = L + 5 by omega, Nat.pow_add]; ring
  rw [hlen]
  congr 1
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.testBit_eq_decide_div_mod_eq (x := q)]
  have hm := @Nat.mod_pow_succ q 2 b
  have h1 : q % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  have h2 : q / 2 ^ b % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [hm]
  generalize q % 2 ^ b = r at h1 ⊢
  generalize q / 2 ^ b % 2 = t at h2 ⊢
  generalize 2 ^ b = w at h1 ⊢
  rcases (by omega : t = 0 ∨ t = 1) with ht | ht <;> subst ht
  · simp only [Nat.mul_zero, Nat.add_zero]
    have h0 : ¬ w ≤ r := by omega
    simp [h0]
  · simp only [Nat.mul_one]
    have h0 : w ≤ r + w := by omega
    have h3 : r + w - w < w := by omega
    simp [h0, h3, h1]

/-- Where bit `i` sits after the doubling steps for bits `≥ b`. -/
def spos (b i : ℕ) : ℕ := i % 2 ^ b + 32 * 2 ^ b * (i / 2 ^ b)

theorem spos_succ (b i : ℕ) : spos b i = spos (b + 1) i + 31 * 2 ^ b * (i / 2 ^ b % 2) := by
  unfold spos
  have hm := @Nat.mod_pow_succ i 2 b
  have hd : i / 2 ^ (b + 1) = i / 2 ^ b / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain ⟨q2, t, hq, ht⟩ : ∃ q2 t, i / 2 ^ b = 2 * q2 + t ∧ t < 2 :=
    ⟨_, _, (Nat.div_add_mod _ 2).symm, Nat.mod_lt _ two_pos⟩
  have hq2 : i / 2 ^ b / 2 = q2 := by rw [hq]; omega
  have hqt : i / 2 ^ b % 2 = t := by rw [hq]; omega
  rw [hm, hd, hq2, hqt, hq, Nat.pow_succ]
  ring

theorem spos_lt {L b i : ℕ} (hi : i < 2 ^ L) : spos b i < 32 * 2 ^ L := by
  unfold spos
  have h := Nat.div_add_mod i (2 ^ b)
  calc i % 2 ^ b + 32 * 2 ^ b * (i / 2 ^ b) ≤ 32 * (2 ^ b * (i / 2 ^ b) + i % 2 ^ b) := by
        nlinarith [Nat.zero_le (i % 2 ^ b)]
    _ = 32 * i := by rw [h]
    _ < 32 * 2 ^ L := by omega

theorem testBit_spos_succ (b i : ℕ) : (spos (b + 1) i).testBit b = i.testBit b := by
  unfold spos
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hm := @Nat.mod_pow_succ i 2 b
  have hr : i % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  have h2 : i / 2 ^ b % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hrew : i % 2 ^ (b + 1) + 32 * 2 ^ (b + 1) * (i / 2 ^ (b + 1)) =
      i % 2 ^ b + 2 ^ b * (i / 2 ^ b % 2 + 64 * (i / 2 ^ (b + 1))) := by
    rw [hm, Nat.pow_succ]; ring
  have hdiv : (i % 2 ^ b + 2 ^ b * (i / 2 ^ b % 2 + 64 * (i / 2 ^ (b + 1)))) / 2 ^ b =
      i / 2 ^ b % 2 + 64 * (i / 2 ^ (b + 1)) := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos b), Nat.div_eq_of_lt hr, Nat.zero_add]
  have key : (i % 2 ^ (b + 1) + 32 * 2 ^ (b + 1) * (i / 2 ^ (b + 1))) / 2 ^ b % 2 =
      i / 2 ^ b % 2 := by
    rw [hrew, hdiv]
    generalize i / 2 ^ b % 2 = t at h2 ⊢
    generalize i / 2 ^ (b + 1) = q
    omega
  rw [key]

/-- One doubling step: the bits whose bit `b` is set move up by `31 * 2^b`. -/
def spreadStep (b L y : ℕ) : ℕ :=
  (y ^^^ (y &&& bitMaskB b L)) ||| ((y &&& bitMaskB b L) <<< (31 * 2 ^ b))

/-- The steps for bits `b - 1` down to `0`. -/
def spreadAux (L : ℕ) : ℕ → ℕ → ℕ
  | 0, y => y
  | b + 1, y => spreadAux L b (spreadStep b L y)

/-- Bit `i` of `x` moves to `32 * i`, for `i < 2^L`. -/
def spread (L x : ℕ) : ℕ := spreadAux L L (x &&& (2 ^ 2 ^ L - 1))

/-- The invariant of the doubling: `y` holds bit `i` of `x` at `spos b i`. -/
def Inv (L b y x : ℕ) : Prop :=
  ∀ p, y.testBit p = true ↔ ∃ i, i < 2 ^ L ∧ p = spos b i ∧ x.testBit i = true

theorem inv_step {L b y x : ℕ} (hb : b < L) (hL : L < 40) (h : Inv L (b + 1) y x) :
    Inv L b (spreadStep b L y) x := by
  intro p
  unfold spreadStep
  rw [Nat.testBit_or, Masks.testBit_remove, Nat.testBit_shiftLeft, Nat.testBit_and,
    testBit_bitMaskB (by omega) hL, testBit_bitMaskB (by omega) hL]
  constructor
  · intro hp
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_true_eq, decide_eq_false_iff_not, ge_iff_le] at hp
    rcases hp with ⟨hy, hM⟩ | ⟨hs, ⟨hy, hlt, hbit⟩⟩
    · obtain ⟨i, hi, rfl, hx⟩ := (h p).mp hy
      refine ⟨i, hi, ?_, hx⟩
      have hcov := spos_lt (b := b + 1) hi
      have hib : i.testBit b = false := by
        rcases hM with hM | hM
        · exact absurd hcov hM
        · rw [← testBit_spos_succ]; exact hM
      rw [spos_succ b i, Nat.testBit_eq_decide_div_mod_eq] at *
      simp only [decide_eq_false_iff_not] at hib
      have : i / 2 ^ b % 2 = 0 := by omega
      rw [this]; ring
    · obtain ⟨i, hi, hpi, hx⟩ := (h (p - 31 * 2 ^ b)).mp hy
      refine ⟨i, hi, ?_, hx⟩
      have hib : i.testBit b = true := by rw [← testBit_spos_succ, ← hpi]; exact hbit
      rw [spos_succ b i, Nat.testBit_eq_decide_div_mod_eq] at *
      simp only [decide_eq_true_eq] at hib
      rw [hib, ← hpi]; omega
  · rintro ⟨i, hi, rfl, hx⟩
    have hcov := spos_lt (b := b + 1) hi
    have hy : y.testBit (spos (b + 1) i) = true := (h _).mpr ⟨i, hi, rfl, hx⟩
    rw [spos_succ b i]
    rcases (Bool.eq_false_or_eq_true (i.testBit b)).symm with hib | hib
    · -- stays: bit `b` of the position is clear
      have h0 : i / 2 ^ b % 2 = 0 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at hib
        simp only [decide_eq_false_iff_not] at hib; omega
      rw [h0, Nat.mul_zero, Nat.add_zero, hy]
      have hM : (spos (b + 1) i).testBit b = false := by rw [testBit_spos_succ]; exact hib
      simp [hM]
    · -- moves: bit `b` of the position is set
      have h1 : i / 2 ^ b % 2 = 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at hib
        simpa using hib
      rw [h1, Nat.mul_one]
      have hM : (spos (b + 1) i).testBit b = true := by rw [testBit_spos_succ]; exact hib
      have hge : spos (b + 1) i + 31 * 2 ^ b ≥ 31 * 2 ^ b := by omega
      have hsub : spos (b + 1) i + 31 * 2 ^ b - 31 * 2 ^ b = spos (b + 1) i := by omega
      simp [hge, hsub, hy, hM, hcov]

theorem inv_spreadAux {L x : ℕ} (hL : L < 40) :
    ∀ (b y : ℕ), b ≤ L → Inv L b y x → Inv L 0 (spreadAux L b y) x
  | 0, y, _, h => h
  | b + 1, y, hb, h => inv_spreadAux hL b _ (by omega) (inv_step (by omega) hL h)

theorem inv_init (L x : ℕ) : Inv L L (x &&& (2 ^ 2 ^ L - 1)) x := by
  intro p
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  constructor
  · intro hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    refine ⟨p, hp.2, ?_, hp.1⟩
    unfold spos
    rw [Nat.mod_eq_of_lt hp.2, Nat.div_eq_of_lt hp.2]; ring
  · rintro ⟨i, hi, rfl, hx⟩
    unfold spos
    rw [Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
    simp [hx, hi]

/-- **What `spread` does**: bit `32 * i` of the result is bit `i` of `x`, for `i < 2^L`,
and nothing else is set. -/
theorem testBit_spread {L : ℕ} (hL : L < 40) (x p : ℕ) :
    (spread L x).testBit p = true ↔ ∃ i, i < 2 ^ L ∧ p = 32 * i ∧ x.testBit i = true := by
  unfold spread
  have h := inv_spreadAux (x := x) hL L _ le_rfl (inv_init L x) p
  rw [h]
  simp only [spos, Nat.pow_zero, Nat.mod_one, Nat.div_one, Nat.zero_add, Nat.mul_one]

theorem spread_eq_packedF {L : ℕ} (hL : L < 40) (x : ℕ) :
    spread L x = packedF (fun j => if x.testBit j then 1 else 0) (2 ^ L) := by
  apply Nat.eq_of_testBit_eq
  intro q
  have hv : ∀ k, (if x.testBit k then 1 else 0) < 2 ^ 32 := by intro k; split <;> norm_num
  rw [testBit_packedF _ hv]
  rcases Bool.eq_false_or_eq_true ((spread L x).testBit q) with hq | hq
  · rw [hq]
    rw [testBit_spread hL] at hq
    obtain ⟨i, hi, rfl, hx⟩ := hq
    have h1 : 32 * i / 32 = i := by omega
    have h2 : 32 * i % 32 = 0 := by omega
    simp [h1, h2, hi, hx]
  · rw [hq]
    have hq' : ¬ ((spread L x).testBit q = true) := by simp [hq]
    rw [testBit_spread hL] at hq'
    simp only [not_exists, not_and] at hq'
    have hq := hq'
    by_cases hd : q / 32 < 2 ^ L
    · by_cases hm : q % 32 = 0
      · have := hq (q / 32) hd (by omega)
        simp [hd, hm, this]
      · simp only [hd, decide_true, Bool.true_and]
        split
        · rw [Nat.testBit_eq_decide_div_mod_eq]
          have : 1 / 2 ^ (q % 32) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))
          simp [this]
        · simp
    · simp [hd]

/-! ### Reading a trace's digits off the masks -/

theorem getD_trCodes (ms : Masks) {p j : ℕ} (hp : p < ms.len) :
    (trCodes ms j).getD p 0 = colourOfDigit (codeAt ms p j) := by
  unfold trCodes
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp]
  rfl

theorem codeAt_lt (ms : Masks) (p j : ℕ) : codeAt ms p j < 3 := by
  unfold codeAt; split_ifs <;> omega

/-- The digit of trace `j` at position `p`, from the colour masks. -/
def digitAt (ms : Masks) (p j : ℕ) : ℕ :=
  (if (ms.colourMask p c2).testBit j then 1 else 0) +
    2 * (if (ms.colourMask p c3).testBit j then 1 else 0)

theorem codeAt_eq_digitAt (ms : Masks) (hc : ms.Consistent) {p j : ℕ} (hp : p < ms.len)
    (hj : j < ms.width) : codeAt ms p j = digitAt ms p j := by
  unfold codeAt digitAt
  by_cases h2 : (ms.colourMask p c2).testBit j = true
  · by_cases h3 : (ms.colourMask p c3).testBit j = true
    · have := (hc p hp).2 j c2 c3 h2 h3 (by simp) (by simp)
      exact absurd this (by decide)
    · simp [h2, h3]
  · by_cases h3 : (ms.colourMask p c3).testBit j = true
    · simp [h2, h3]
    · simp [h2, h3]

/-! ### The packed table of bulk indices -/

/-- Lane `j` holds `Σ_{p < m} 3^p * digit_p(j)`, the bulk index of trace `j`: digit `1`
is colour `c2`, digit `2` colour `c3`. -/
def packIdx (ms : Masks) (m L : ℕ) : ℕ :=
  (List.range m).foldr (fun p acc =>
    3 ^ p * (spread L (ms.colourMask p c2) + 2 * spread L (ms.colourMask p c3)) + acc) 0

/-- The lane values, as a function. -/
def laneVal (ms : Masks) (m j : ℕ) : ℕ :=
  (List.range m).foldr (fun p acc => 3 ^ p * digitAt ms p j + acc) 0

/-- A fold that adds up terms is the sum plus the initial value. -/
theorem foldr_add_init (g : ℕ → ℕ) : ∀ (l : List ℕ) (init : ℕ),
    l.foldr (fun p acc => g p + acc) init = l.foldr (fun p acc => g p + acc) 0 + init
  | [], _ => by simp
  | p :: l, init => by simp only [List.foldr_cons, foldr_add_init g l init]; ring

theorem digitAt_le (ms : Masks) (p j : ℕ) : digitAt ms p j ≤ 3 := by
  unfold digitAt; split <;> split <;> omega

theorem laneVal_succ (ms : Masks) (m j : ℕ) :
    laneVal ms (m + 1) j = 3 ^ m * digitAt ms m j + laneVal ms m j := by
  unfold laneVal
  rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero,
    foldr_add_init]
  ring

theorem laneVal_lt (ms : Masks) (m j : ℕ) : laneVal ms m j < 2 * 3 ^ m := by
  induction m with
  | zero => simp [laneVal]
  | succ m ih =>
    rw [laneVal_succ, Nat.pow_succ]
    have hd := digitAt_le ms m j
    have : 3 ^ m * digitAt ms m j ≤ 3 ^ m * 3 := Nat.mul_le_mul_left _ hd
    omega

theorem packIdx_succ (ms : Masks) (m L : ℕ) :
    packIdx ms (m + 1) L =
      3 ^ m * (spread L (ms.colourMask m c2) + 2 * spread L (ms.colourMask m c3)) + packIdx ms m L := by
  unfold packIdx
  rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero,
    foldr_add_init]
  ring

theorem packIdx_eq_packedF {L : ℕ} (hL : L < 40) (ms : Masks) (m : ℕ) :
    packIdx ms m L = packedF (fun j => laneVal ms m j) (2 ^ L) := by
  induction m with
  | zero => simp [packIdx, laneVal, packedF_zero]
  | succ m ih =>
    have hfun : (fun j => laneVal ms (m + 1) j) =
        fun j => 3 ^ m * ((fun j => if (ms.colourMask m c2).testBit j then 1 else 0) j +
          (fun j => 2 * (fun j => if (ms.colourMask m c3).testBit j then 1 else 0) j) j) +
          (fun j => laneVal ms m j) j :=
      funext fun j => by rw [laneVal_succ]; rfl
    rw [packIdx_succ, ih, hfun, packedF_add, packedF_mul, packedF_add, packedF_mul,
      spread_eq_packedF hL, spread_eq_packedF hL]

/-- **Lane `j` of the table is the bulk index of trace `j`.** -/
theorem lane_packIdx (ms : Masks) (hc : ms.Consistent) {m L : ℕ} (hL : L < 40)
    (hm : 2 * 3 ^ m < 2 ^ 32) (hlen : m ≤ ms.len) (hw : ms.width ≤ 2 ^ L) {j : ℕ}
    (hj : j < ms.width) : lane (packIdx ms m L) j = bigOf ms m j := by
  rw [packIdx_eq_packedF hL, lane_packedF _ (fun k => lt_of_lt_of_le (laneVal_lt ms m k) hm.le)
    (2 ^ L) j (lt_of_lt_of_le hj hw)]
  -- both sides are the same fold over the positions
  unfold bigOf idxAux laneVal
  have key : ∀ l : List ℕ, (∀ p ∈ l, p < ms.len) →
      l.foldr (fun k acc => digitOfColour ((trCodes ms j).getD k 0) * 3 ^ k + acc) 0 =
        l.foldr (fun p acc => 3 ^ p * digitAt ms p j + acc) 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons p l ih =>
      simp only [List.foldr_cons]
      rw [ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
      congr 1
      rw [Nat.mul_comm]
      congr 1
      have hp := hl p List.mem_cons_self
      rw [getD_trCodes ms hp, digitOfColour_colourOfDigit _ (codeAt_lt ms p j)]
      exact codeAt_eq_digitAt ms hc hp hj
  exact (key _ (fun p hp => lt_of_lt_of_le (List.mem_range.mp hp) hlen)).symm

end Bulk
end FourColor

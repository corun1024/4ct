import FourColor.Bulk.Flip
import FourColor.Bulk.Perms

/-!
# From the bulk checks to the Kempe certificate

A configuration's bulk data are rank planes `R` (the rank of every trace, the
all-ones value meaning "not certified"), witness planes `H` (the least rank
among the six colour permutations of each trace), choice planes `C` (the
position each certified trace is argued with) and the mask `goodAll` of the
colourings up to permutation.  Six checks, all decidable, are asked of them:

* `H = minPerm m R`;
* the rank-`0` traces lie in `goodAll`;
* every certified trace's chosen position holds `c2` or `c3`, and is a
  position at all;
* for every pair `p < q ≤ m`, `pairOk`.

`hcert_of_bulk` turns them into the obligation of `kempeCoclosure_of_rank`:
every certified trace answers every chromogram with a flipped trace that is a
colouring, or permutes into the certified set at strictly smaller rank.
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Masks from predicates -/

/-- The mask with bit `r < n` set when `P r`. -/
def maskOf (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if P n then 2 ^ n else 0) ||| maskOf P n

theorem testBit_maskOf (P : ℕ → Bool) (n r : ℕ) :
    (maskOf P n).testBit r = (decide (r < n) && P r) := by
  induction n with
  | zero => simp [maskOf]
  | succ n ih =>
    simp only [maskOf, Nat.testBit_or, ih]
    by_cases hr : r = n
    · subst hr
      cases h : P r <;> simp [h, Nat.testBit_two_pow]
    · have : (if P n then 2 ^ n else 0).testBit r = false := by
        split_ifs <;> simp [Nat.testBit_two_pow, Ne.symm hr]
      rw [this]
      by_cases hlt : r < n
      · simp [hlt, (by omega : r < n + 1)]
      · simp [hlt, (show ¬ r < n + 1 by omega)]

/-! ### Rank planes -/

/-- Traces whose every plane bit is set: the top rank, "not certified". -/
def allOnes (m : ℕ) (R : List ℕ) : ℕ := R.foldr (· &&& ·) (2 ^ 3 ^ m - 1)

/-- Traces with some plane bit set: rank above zero. -/
def anyOne (R : List ℕ) : ℕ := R.foldr (· ||| ·) 0

/-- The top rank value. -/
def rankTop (R : List ℕ) : ℕ := 2 ^ R.length - 1

/-- The certified traces: rank below the top. -/
def certMask (m : ℕ) (R : List ℕ) : ℕ := (2 ^ 3 ^ m - 1) ^^^ allOnes m R

/-- The rank-zero traces. -/
def zeroMask (m : ℕ) (R : List ℕ) : ℕ := (2 ^ 3 ^ m - 1) ^^^ anyOne R

/-- Certified traces of positive rank: the ones that need an argument. -/
def nonZero (m : ℕ) (R : List ℕ) : ℕ := certMask m R &&& anyOne R

theorem testBit_allOnes (m : ℕ) (R : List ℕ) (i : ℕ) (hi : i < 3 ^ m) :
    (allOnes m R).testBit i = decide (val R i = rankTop R) := by
  unfold allOnes rankTop
  induction R with
  | nil => simp [val, Nat.testBit_two_pow_sub_one, hi]
  | cons a as ih =>
    simp only [List.foldr_cons, Nat.testBit_and, ih, val, List.length_cons]
    have hb := val_lt_two_pow as i
    have h2 : 2 ^ (as.length + 1) = 2 * 2 ^ as.length := by rw [Nat.pow_succ]; ring
    have hpos : 0 < 2 ^ as.length := by positivity
    rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha <;> simp [ha] <;> omega

theorem testBit_anyOne (R : List ℕ) (i : ℕ) : (anyOne R).testBit i = decide (0 < val R i) := by
  unfold anyOne
  induction R with
  | nil => simp [val]
  | cons a as ih =>
    simp only [List.foldr_cons, Nat.testBit_or, ih, val]
    rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha <;> simp [ha] <;> omega

theorem testBit_certMask {m : ℕ} (R : List ℕ) {i : ℕ} (hi : i < 3 ^ m) :
    (certMask m R).testBit i = decide (val R i < rankTop R) := by
  unfold certMask
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, testBit_allOnes m R i hi]
  have := val_lt_two_pow R i
  unfold rankTop
  simp only [hi, decide_true, Bool.true_xor]
  by_cases h : val R i = 2 ^ R.length - 1
  · simp [h]
  · have : val R i < 2 ^ R.length - 1 := by omega
    simp [h, this]

theorem testBit_zeroMask {m : ℕ} (R : List ℕ) {i : ℕ} (hi : i < 3 ^ m) :
    (zeroMask m R).testBit i = decide (val R i = 0) := by
  unfold zeroMask
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, testBit_anyOne]
  simp only [hi, decide_true, Bool.true_xor]
  by_cases h : val R i = 0 <;> simp [h] <;> omega

theorem testBit_nonZero {m : ℕ} (R : List ℕ) {i : ℕ} (hi : i < 3 ^ m) :
    (nonZero m R).testBit i = decide (0 < val R i ∧ val R i < rankTop R) := by
  unfold nonZero
  rw [Nat.testBit_and, testBit_certMask R hi, testBit_anyOne]
  by_cases h1 : 0 < val R i <;> by_cases h2 : val R i < rankTop R <;> simp [h1, h2]

/-! ### The closure of a mask under colour permutations -/

/-- The traces some colour permutation of which lies in `Φ`. -/
def permClose (m : ℕ) (Φ : ℕ) : ℕ := allPerms.foldr (fun g acc => permMask g m Φ ||| acc) 0

theorem testBit_permClose (m Φ i : ℕ) (hi : i < 3 ^ m) :
    (permClose m Φ).testBit i = true ↔ ∃ g : EdgePerm, Φ.testBit (permIdx g m i) = true := by
  unfold permClose
  constructor
  · intro h
    suffices key : ∀ L : List EdgePerm,
        (L.foldr (fun g acc => permMask g m Φ ||| acc) 0).testBit i = true →
        ∃ g : EdgePerm, Φ.testBit (permIdx g m i) = true from key allPerms h
    intro L
    induction L with
    | nil => simp
    | cons g L ih =>
      intro h
      rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, testBit_permMask g Φ i hi] at h
      rcases h with h | h
      · exact ⟨g⁻¹, h⟩
      · exact ih h
  · rintro ⟨g, hg⟩
    suffices key : ∀ L : List EdgePerm, g⁻¹ ∈ L →
        (L.foldr (fun g acc => permMask g m Φ ||| acc) 0).testBit i = true from
      key allPerms (mem_allPerms _)
    intro L
    induction L with
    | nil => simp
    | cons g' L ih =>
      intro hmem
      rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, testBit_permMask g' Φ i hi]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · left; rw [inv_inv]; exact hg
      · right; exact ih hmem'

theorem permClose_permIdx (m Φ : ℕ) (g : EdgePerm) (i : ℕ) (hi : i < 3 ^ m) :
    (permClose m Φ).testBit (permIdx g m i) = (permClose m Φ).testBit i := by
  have hgi := permIdx_lt g hi
  cases h : (permClose m Φ).testBit i
  · cases h' : (permClose m Φ).testBit (permIdx g m i)
    · rfl
    · exfalso
      obtain ⟨h', hh⟩ := (testBit_permClose m Φ _ hgi).mp h'
      rw [permIdx_permIdx h' g hi] at hh
      have := (testBit_permClose m Φ i hi).mpr ⟨h' * g, hh⟩
      rw [h] at this; exact absurd this (by simp)
  · obtain ⟨h', hh⟩ := (testBit_permClose m Φ i hi).mp h
    apply (testBit_permClose m Φ _ hgi).mpr
    refine ⟨h' * g⁻¹, ?_⟩
    rw [permIdx_permIdx _ _ hi, mul_assoc, inv_mul_cancel, mul_one]
    exact hh

/-! ### The predicates of the certificate -/

/-- Colourings, up to permutation: the traces `goodAll` names. -/
def PGood (m : ℕ) (goodAll : ℕ) (et : List Color) : Prop :=
  ∃ j, j < 3 ^ m ∧ goodAll.testBit j = true ∧ et = traceOf m j

/-- The certified traces of positive rank. -/
def SCert (m : ℕ) (R : List ℕ) (et : List Color) : Prop :=
  ∃ j, j < 3 ^ m ∧ 0 < val R j ∧ val R j < rankTop R ∧ et = traceOf m j

/-- The rank of a trace, read from its index. -/
def rankOf (m : ℕ) (R : List ℕ) (et : List Color) : ℕ := val R (indexOf m et)

theorem rankOf_traceOf (m : ℕ) (R : List ℕ) {i : ℕ} (hi : i < 3 ^ m) :
    rankOf m R (traceOf m i) = val R i := by
  rw [rankOf, indexOf_traceOf m i hi]

/-! ### Small bridges -/

theorem digit_ne_zero_of_getD {m i k : ℕ} (hk : k < m) (h : (traceOf m i).getD k 0 ≠ c1) :
    digit k i ≠ 0 := by
  rw [getD_traceOf_lt hk] at h
  intro h0
  exact h (by rw [h0]; rfl)

theorem getD_ne_c1_of_digit {m i k : ℕ} (hk : k < m) (h : digit k i ≠ 0) :
    (traceOf m i).getD k 0 ≠ c1 := by
  rw [getD_traceOf_lt hk]
  intro hc
  exact h ((colourOfDigit_eq_c1_iff _).mp hc)

theorem c2_or_c3_of_ne {c : Color} (h1 : c ≠ c1) (h0 : c ≠ 0) : c = c2 ∨ c = c3 := by
  cases c <;> simp_all

theorem nonC1_bit_of_getD {m i p : ℕ} (hp : p ≤ m) (hi : i < 3 ^ m)
    (h0 : (0 : Color) ∉ traceOf m i) (h : (traceOf m i).getD p 0 ≠ c1) :
    (nonC1 m p).testBit i = true := by
  rw [testBit_nonC1 hp]
  have hmem : (traceOf m i).getD p 0 ∈ traceOf m i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    exact List.getElem_mem _
  have hne0 : (traceOf m i).getD p 0 ≠ 0 := fun hz => h0 (hz ▸ hmem)
  simp only [decide_eq_true_eq]
  exact ⟨hi, c2_or_c3_of_ne h hne0⟩

/-- **One candidate flip suffices.**  Given a flip along the chromogram whose
toggled index has a witness rank below the trace's rank, the certificate
obligation for that chromogram holds. -/
theorem finish_of_lt {m : ℕ} {R H : List ℕ} {goodAll : ℕ} (hH : H = minPerm m R)
    (hgood : zeroMask m R &&& ((2 ^ 3 ^ m - 1) ^^^ goodAll) = 0)
    (hgoodPerm : ∀ (g : EdgePerm) (j : ℕ), j < 3 ^ m →
      goodAll.testBit (permIdx g m j) = goodAll.testBit j)
    {i : ℕ} (hi : i < 3 ^ m) (htop : val R i < rankTop R) {w : Chromogram}
    (hbal : balanced 0 false w = true)
    (L : List ℕ) (hL : L.Nodup) (M : ℕ)
    (hM : ∀ k, k < m → (M.testBit k = true ↔ (k ∈ L ∧ digit k i ≠ 0)))
    (hflip : matchg [] (flipFromB M 0 (traceOf m i)) w = true)
    (hlt : val H (togIdxs m L i) < val R i) :
    ∃ et', matchg [] et' w = true ∧
      (PGood m goodAll et' ∨
        ∃ g : EdgePerm, SCert m R (et'.map g) ∧ rankOf m R (et'.map g) < rankOf m R (traceOf m i)) := by
  have hsum : (flipFromB M 0 (traceOf m i)).sum = 0 := sum_eq_zero_of_matchg hbal hflip
  have het' := traceOf_togIdxs L hL i M hM hsum
  set j' := togIdxs m L i with hj'
  have hj'lt : j' < 3 ^ m := togIdxs_lt hi L
  refine ⟨traceOf m j', by rw [het']; exact hflip, ?_⟩
  rw [hH] at hlt
  obtain ⟨g, hg⟩ := exists_val_minPerm R j' hj'lt
  rw [hg] at hlt
  set j := permIdx g m j' with hjdef
  have hjlt : j < 3 ^ m := permIdx_lt g hj'lt
  by_cases hz : val R j = 0
  · -- a colouring, up to permutation
    left
    have hzb : (zeroMask m R).testBit j = true := by rw [testBit_zeroMask R hjlt]; simp [hz]
    have hgb : goodAll.testBit j = true := by
      have := congrArg (fun x => x.testBit j) hgood
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
        hzb, hjlt, decide_true, Bool.true_and, Bool.true_xor] at this
      cases h : goodAll.testBit j
      · rw [h] at this; exact absurd this (by simp)
      · rfl
    rw [hjdef, hgoodPerm g j' hj'lt] at hgb
    exact ⟨j', hj'lt, hgb, rfl⟩
  · right
    refine ⟨g, ⟨j, hjlt, by omega, by omega, ?_⟩, ?_⟩
    · rw [hjdef, traceOf_permIdx]
    · rw [← traceOf_permIdx, ← hjdef, rankOf_traceOf m R hjlt, rankOf_traceOf m R hi]
      exact hlt

/-! ### The assembly -/

/-- **The bulk checks yield the certificate obligation.** -/
theorem hcert_of_bulk {m : ℕ} {R H C : List ℕ} {goodAll : ℕ}
    (hlenH : R.length = H.length) (hH : H = minPerm m R)
    (hClen : m < 2 ^ C.length)
    (hgood : zeroMask m R &&& ((2 ^ 3 ^ m - 1) ^^^ goodAll) = 0)
    (hgoodPerm : ∀ (g : EdgePerm) (j : ℕ), j < 3 ^ m →
      goodAll.testBit (permIdx g m j) = goodAll.testBit j)
    (hchoice1 : ∀ p, p ≤ m →
      choiceMask m C (nonZero m R) p &&& ((2 ^ 3 ^ m - 1) ^^^ nonC1 m p) = 0)
    (hchoice2 : ∀ i, i < 3 ^ m → (nonZero m R).testBit i = true → val C i ≤ m)
    (hpairs : ∀ p q, p < q → q ≤ m →
      pairOk m p q R H (choiceMask m C (nonZero m R) p ||| choiceMask m C (nonZero m R) q) = true) :
    ∀ et, SCert m R et → ∀ w, matchg [] et w = true →
      ∃ et', matchg [] et' w = true ∧
        (PGood m goodAll et' ∨
          ∃ g : EdgePerm, SCert m R (et'.map g) ∧ rankOf m R (et'.map g) < rankOf m R et) := by
  rintro et ⟨i, hi, hpos, htop, rfl⟩ w hm
  have h0 : (0 : Color) ∉ traceOf m i := matchg_notMem_zero _ _ _ hm
  have hbal : balanced 0 false w = true := by
    have h := (matchg_balanced hm).2
    simpa [traceOf] using h
  -- the trace is certified, of positive rank, with a chosen position
  have hcert : (certMask m R).testBit i = true := by
    rw [testBit_certMask R hi]; simpa using htop
  have hnz : (nonZero m R).testBit i = true := by
    rw [testBit_nonZero R hi]; simp [hpos, htop]
  set p := val C i with hp
  have hpm : p ≤ m := hchoice2 i hi hnz
  have hp2 : p < 2 ^ C.length := lt_of_le_of_lt hpm hClen
  have hchoice : (choiceMask m C (nonZero m R) p).testBit i = true := by
    rw [testBit_choiceMask C _ p i hi hp2, hnz]; simp [hp]
  have hnonc1 : (nonC1 m p).testBit i = true := by
    have := congrArg (fun x => x.testBit i) (hchoice1 p hpm)
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
      hchoice, hi, decide_true, Bool.true_and, Bool.true_xor] at this
    cases h : (nonC1 m p).testBit i
    · rw [h] at this; exact absurd this (by simp)
    · rfl
  have hpc : (traceOf m i).getD p 0 ≠ c1 := by
    rw [testBit_nonC1 hpm] at hnonc1
    simp only [decide_eq_true_eq] at hnonc1
    rcases hnonc1.2 with h | h <;> rw [h] <;> decide
  -- the partner of `p` in `w`
  obtain ⟨q, hq, hqp, hqc, heven, hf1, hf2, hf3⟩ :=
    partner_exists hm (p := p) (by simp; omega) hpc
  have hqm : q ≤ m := by simp at hq; omega
  -- work with the ordered pair
  set lo := min p q with hlo
  set hi' := max p q with hhi'
  have hlohi : lo < hi' := by
    rcases Nat.lt_or_gt_of_ne hqp with h | h
    · rw [hlo, hhi', min_eq_right h.le, max_eq_left h.le]; exact h
    · rw [hlo, hhi', min_eq_left h.le, max_eq_right h.le]; exact h
  have hhim : hi' ≤ m := by rw [hhi']; omega
  have hloc : (traceOf m i).getD lo 0 ≠ c1 := by
    rw [hlo]; rcases le_total p q with h | h
    · rw [min_eq_left h]; exact hpc
    · rw [min_eq_right h]; exact hqc
  have hhic : (traceOf m i).getD hi' 0 ≠ c1 := by
    rw [hhi']; rcases le_total p q with h | h
    · rw [max_eq_right h]; exact hqc
    · rw [max_eq_left h]; exact hpc
  -- compatibility of the pair
  have hcmp : (compat m lo hi').testBit i = true := by
    rw [testBit_compat hlohi hhim]
    simp only [decide_eq_true_eq]
    refine ⟨hi, ?_, ?_, ?_⟩
    · have := nonC1_bit_of_getD (by omega) hi h0 hloc
      rw [testBit_nonC1 (by omega)] at this
      simp only [decide_eq_true_eq] at this
      exact this.2
    · have := nonC1_bit_of_getD hhim hi h0 hhic
      rw [testBit_nonC1 hhim] at this
      simp only [decide_eq_true_eq] at this
      exact this.2
    · rw [nonC1Count_eq hlohi hhim h0, min_eq_left hlohi.le, max_eq_right hlohi.le]
      rw [length_traceOf] at heven
      exact Nat.even_iff.mp heven
  -- the pair's choice mask holds `i`
  have hcpair : (choiceMask m C (nonZero m R) lo ||| choiceMask m C (nonZero m R) hi').testBit i
      = true := by
    rw [Nat.testBit_or]
    rcases le_total p q with h | h
    · rw [hlo, min_eq_left h, hchoice]; simp
    · rw [hhi', max_eq_left h, hchoice]; simp
  have hHinv : ∀ j, j < 3 ^ m → val H (togIdxs m (List.range' 0 (m + 1)) j) = val H j := by
    intro j hj; rw [hH]; exact val_minPerm_togAll R j hj
  have hspec := pairOk_spec hlohi hhim hlenH hHinv (hpairs lo hi' hlohi hhim) i hi hcpair hcmp
  -- the masks of the three candidate flips
  have hn : (traceOf m i).length = m + 1 := by simp
  have hdig : ∀ k, k < m → ((traceOf m i).getD k 0 ≠ c1 ↔ digit k i ≠ 0) :=
    fun k hk => ⟨digit_ne_zero_of_getD hk, getD_ne_c1_of_digit hk⟩
  have hplo : lo = p ∨ hi' = p := by
    rcases le_total p q with h | h
    · left; rw [hlo, min_eq_left h]
    · right; rw [hhi', max_eq_left h]
  have hmem_pair : ∀ r, (r = p ∨ r = q) ↔ (r = lo ∨ r = hi') := by
    intro r
    rcases le_total p q with h | h
    · rw [hlo, hhi', min_eq_left h, max_eq_right h]
    · rw [hlo, hhi', min_eq_right h, max_eq_left h]; tauto
  have hlom : lo < m := by omega
  have hdlo : digit lo i ≠ 0 := digit_ne_zero_of_getD hlom hloc
  have hdhi : hi' < m → digit hi' i ≠ 0 := fun h => digit_ne_zero_of_getD h hhic
  rcases hspec with hlt | hlt | hlt
  · -- the chord alone
    let M := maskOf (fun r => decide (r = p ∨ r = q)) (m + 1)
    have hMbit : ∀ r, M.testBit r = true ↔ (r = p ∨ r = q) := by
      intro r
      rw [testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        rcases h with h | h <;> rw [h] <;> omega
    refine finish_of_lt hH hgood hgoodPerm hi htop hbal [lo, hi'] (by simp; omega) M ?_
      (matchg_flip M w _ 0 [] [] hm (hf1 M hMbit)) hlt
    intro k hk
    rw [hMbit, hmem_pair]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h)
      · exact ⟨Or.inl h, by rw [h]; exact hdlo⟩
      · exact ⟨Or.inr h, by rw [h]; exact hdhi (by omega)⟩
    · rintro ⟨h, -⟩; exact h
  · -- everything strictly inside
    let M := maskOf (fun r => decide (lo < r ∧ r < hi' ∧ (traceOf m i).getD r 0 ≠ c1)) (m + 1)
    have hMbit : ∀ r, M.testBit r = true ↔ (lo < r ∧ r < hi' ∧ (traceOf m i).getD r 0 ≠ c1) := by
      intro r
      rw [testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by omega, h⟩
    refine finish_of_lt hH hgood hgoodPerm hi htop hbal (inside lo hi') (List.nodup_range' 1 Nat.one_pos) M ?_
      (matchg_flip M w _ 0 [] [] hm (hf2 M hMbit)) hlt
    intro k hk
    rw [hMbit, inside, List.mem_range'_1, ← hdig k hk]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, by omega, h3⟩
  · -- the chord together with everything inside
    let M := maskOf (fun r => decide (r = p ∨ r = q ∨
      (lo < r ∧ r < hi' ∧ (traceOf m i).getD r 0 ≠ c1))) (m + 1)
    have hMbit : ∀ r, M.testBit r = true ↔
        (r = p ∨ r = q ∨ (lo < r ∧ r < hi' ∧ (traceOf m i).getD r 0 ≠ c1)) := by
      intro r
      rw [testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        rcases h with h | h | ⟨-, h2, -⟩ <;> first | (rw [h]; omega) | omega
    have hnodup : (lo :: hi' :: inside lo hi').Nodup := by
      rw [List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, List.nodup_range' 1 Nat.one_pos⟩
      · simp [inside, List.mem_range'_1]; omega
      · simp [inside, List.mem_range'_1]; omega
    refine finish_of_lt hH hgood hgoodPerm hi htop hbal (lo :: hi' :: inside lo hi') hnodup M ?_
      (matchg_flip M w _ 0 [] [] hm (hf3 M hMbit)) hlt
    intro k hk
    have hpq : (k = p ∨ k = q ∨ (lo < k ∧ k < hi' ∧ (traceOf m i).getD k 0 ≠ c1)) ↔
        (k = lo ∨ k = hi' ∨ (lo < k ∧ k < hi' ∧ (traceOf m i).getD k 0 ≠ c1)) := by
      rw [← or_assoc, hmem_pair, or_assoc]
    rw [hMbit, hpq, ← hdig k hk]
    simp only [List.mem_cons, inside, List.mem_range'_1]
    constructor
    · rintro (h | h | ⟨h1, h2, h3⟩)
      · exact ⟨Or.inl h, by rw [h]; exact hloc⟩
      · exact ⟨Or.inr (Or.inl h), by rw [h]; exact hhic⟩
      · exact ⟨Or.inr (Or.inr ⟨by omega, by omega⟩), h3⟩
    · rintro ⟨h | h | ⟨h1, h2⟩, h3⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨by omega, by omega, h3⟩)

end Bulk
end FourColor

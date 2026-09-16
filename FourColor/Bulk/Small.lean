import FourColor.MaskCert
import FourColor.Bulk.Index

/-!
# Between the small universe and the bulk universe

The residual certificate of a configuration lives in a small universe of
traces described by colour masks (`Masks`), while the bulk certificate lives in
the universe of all `3 ^ m` traces.  This file reads a small-universe trace's
bulk index off its colour masks (`bigOf`), shows the two traces agree when the
completing colour is right (`traceOf_bigOf`), and provides the two cheap ways
of touching a bulk mask from narrow computations: membership through
`2 ^ 16`-bit pieces (`memPiece`), and building a sparse mask piece by piece
(`buildMask`), so that no narrow step ever creates a wide intermediate.
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Reading a small-universe trace -/

/-- The digit code of trace `j`'s colour at position `p`, from the colour masks. -/
def codeAt (ms : Masks) (p j : ℕ) : ℕ :=
  if (ms.colourMask p c2).testBit j then 1 else if (ms.colourMask p c3).testBit j then 2 else 0

theorem codeAt_eq (ms : Masks) (hc : ms.Consistent) {p j : ℕ} (hp : p < ms.len)
    (hj : j < ms.width) : codeAt ms p j = digitOfColour (ms.colourAt p j) := by
  have h2 := ms.colourAt_eq_iff hp hj hc (c := c2) (by simp)
  have h3 := ms.colourAt_eq_iff hp hj hc (c := c3) (by simp)
  have h0 := ms.colourAt_ne_c0 hp hj hc
  unfold codeAt
  cases hcol : ms.colourAt p j
  · exact absurd hcol h0
  · have : ¬ (ms.colourMask p c2).testBit j := fun h => by rw [hcol] at h2; exact absurd (h2.mpr h) (by decide)
    have : ¬ (ms.colourMask p c3).testBit j := fun h => by rw [hcol] at h3; exact absurd (h3.mpr h) (by decide)
    simp [*, digitOfColour]
  · have : (ms.colourMask p c2).testBit j := h2.mp hcol
    simp [this, digitOfColour]
  · have hn2 : ¬ (ms.colourMask p c2).testBit j := fun h => by rw [hcol] at h2; exact absurd (h2.mpr h) (by decide)
    have : (ms.colourMask p c3).testBit j := h3.mp hcol
    simp [hn2, this, digitOfColour]

/-- The colours of trace `j`, read from the masks (a computable `Masks.traceOf`). -/
def trCodes (ms : Masks) (j : ℕ) : List Color :=
  (List.range ms.len).map fun p => colourOfDigit (codeAt ms p j)

theorem trCodes_eq (ms : Masks) (hc : ms.Consistent) {j : ℕ} (hj : j < ms.width) :
    trCodes ms j = ms.traceOf j := by
  unfold trCodes Masks.traceOf
  apply List.map_congr_left
  intro p hp
  rw [List.mem_range] at hp
  rw [codeAt_eq ms hc hp hj, colourOfDigit_digitOfColour (ms.colourAt_ne_c0 hp hj hc)]

@[simp] theorem length_trCodes (ms : Masks) (j : ℕ) : (trCodes ms j).length = ms.len := by
  simp [trCodes]

/-- The bulk index of small-universe trace `j`: its first `m` colours as digits. -/
def bigOf (ms : Masks) (m j : ℕ) : ℕ := idxAux (trCodes ms j) m

theorem bigOf_lt (ms : Masks) (m j : ℕ) : bigOf ms m j < 3 ^ m := idxAux_lt _ m

/-- The completing colour of trace `j` is the sum of its first `m` colours. -/
def lastOk (ms : Masks) (m j : ℕ) : Bool :=
  decide ((trCodes ms j).getD m 0 = (partialOf m (bigOf ms m j)).sum)

theorem partialOf_bigOf (ms : Masks) (m j : ℕ) (hm : m ≤ ms.len) :
    partialOf m (bigOf ms m j) = (trCodes ms j).take m := by
  apply List.ext_getElem
  · simp [hm]
  · intro k hk1 hk2
    have hk : k < m := by simpa using hk1
    rw [getElem_partialOf m _ k hk, bigOf, digit_idxAux _ m k hk, List.getElem_take]
    have hkl : k < (trCodes ms j).length := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl]
    simp only [Option.getD_some]
    have hne : (trCodes ms j)[k] ≠ 0 := by
      simp only [trCodes, List.getElem_map, List.getElem_range]
      exact colourOfDigit_ne_zero _
    rw [colourOfDigit_digitOfColour hne]

/-- **A small-universe trace is its bulk trace** when the completion agrees. -/
theorem traceOf_bigOf (ms : Masks) (hc : ms.Consistent) {m : ℕ} (hlen : ms.len = m + 1)
    {j : ℕ} (hj : j < ms.width) (hlast : lastOk ms m j = true) :
    traceOf m (bigOf ms m j) = ms.traceOf j := by
  rw [← trCodes_eq ms hc hj, traceOf, completeTrace, partialOf_bigOf ms m j (by omega)]
  unfold lastOk at hlast
  rw [decide_eq_true_eq, partialOf_bigOf ms m j (by omega)] at hlast
  rw [← hlast]
  -- a list of length `m + 1` is its first `m` entries followed by its last
  have hl : (trCodes ms j).length = m + 1 := by simp [hlen]
  conv_rhs => rw [← List.take_append_drop m (trCodes ms j)]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  have := List.drop_eq_getElem_cons (l := trCodes ms j) (i := m) (by omega)
  rw [this]
  have : (trCodes ms j).drop (m + 1) = [] := List.drop_of_length_le (by omega)
  rw [this]

/-! ### Touching a bulk mask from narrow computations -/

/-- The width of a piece. -/
def pieceBits : ℕ := 65536

/-- The `k` pieces of `M`, least significant first. -/
def pieces (M k : ℕ) : List ℕ :=
  (List.range k).map fun c => (M >>> (c * pieceBits)) &&& (2 ^ pieceBits - 1)

/-- Bit `i` of a mask given by its pieces. -/
def memPiece (P : List ℕ) (i : ℕ) : Bool := (P.getD (i / pieceBits) 0).testBit (i % pieceBits)

theorem memPiece_pieces (M k i : ℕ) (hi : i < k * pieceBits) :
    memPiece (pieces M k) i = M.testBit i := by
  unfold memPiece pieces
  have hpos : 0 < pieceBits := by decide
  have hc : i / pieceBits < k := by
    rw [Nat.div_lt_iff_lt_mul hpos]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  simp only [Option.map_some, Option.getD_some]
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  have hmod : i % pieceBits < pieceBits := Nat.mod_lt _ hpos
  rw [show i / pieceBits * pieceBits + i % pieceBits = i from Nat.div_add_mod' i pieceBits]
  simp [hmod]

/-- A mask from lists of offsets, one list per piece. -/
def buildMask : List (List ℕ) → ℕ
  | [] => 0
  | ks :: rest => (ks.foldr (fun k acc => acc ||| 2 ^ k) 0) ||| (buildMask rest <<< pieceBits)

theorem testBit_foldr_pow (ks : List ℕ) (i : ℕ) :
    (ks.foldr (fun k acc => acc ||| 2 ^ k) 0).testBit i = decide (i ∈ ks) := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.foldr_cons, Nat.testBit_or, ih, Nat.testBit_two_pow, List.mem_cons]
    by_cases h : k = i <;> by_cases h' : i ∈ ks <;> simp [h, h']
    omega

/-- Bit `c * pieceBits + off` of a built mask is the membership of `off` in piece `c`. -/
theorem testBit_buildMask (L : List (List ℕ)) (hL : ∀ ks ∈ L, ∀ k ∈ ks, k < pieceBits)
    (c off : ℕ) (hoff : off < pieceBits) :
    (buildMask L).testBit (c * pieceBits + off) = decide (off ∈ L.getD c []) := by
  induction L generalizing c with
  | nil => simp [buildMask]
  | cons ks rest ih =>
    simp only [buildMask, Nat.testBit_or, Nat.testBit_shiftLeft]
    have hks : ∀ k ∈ ks, k < pieceBits := hL ks (List.mem_cons_self ..)
    have hrest : ∀ ks' ∈ rest, ∀ k ∈ ks', k < pieceBits :=
      fun ks' h => hL ks' (List.mem_cons_of_mem _ h)
    cases c with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, testBit_foldr_pow, List.getD_cons_zero]
      have : ¬ pieceBits ≤ off := by omega
      simp [this]
    | succ c =>
      rw [testBit_foldr_pow]
      have hle : pieceBits ≤ (c + 1) * pieceBits + off := by
        have : pieceBits ≤ (c + 1) * pieceBits := Nat.le_mul_of_pos_left _ (by omega)
        omega
      have heq : (c + 1) * pieceBits + off - pieceBits = c * pieceBits + off := by
        rw [Nat.succ_mul]; omega
      rw [heq, ih hrest c, List.getD_cons_succ]
      have hno : off + pieceBits * c + pieceBits ∉ ks := fun h => by
        have := hks _ h; omega
      have : decide ((c + 1) * pieceBits + off ∈ ks) = false := by
        simp only [decide_eq_false_iff_not]
        intro h; have := hks _ h
        have : pieceBits ≤ (c + 1) * pieceBits := Nat.le_mul_of_pos_left _ (by omega)
        omega
      rw [this]
      simp [hle]

end Bulk
end FourColor

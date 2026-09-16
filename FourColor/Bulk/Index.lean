import FourColor.Bulk.Flip

/-!
# Every zero-free colour list is the digit list of its index

`indexOf m et` reads a colour list back into an index; here it is shown to be
below `3 ^ m` and to have the list's colours as digits, so that a trace found
in a tree can be located in a bulk mask.
-/

namespace FourColor
namespace Bulk

open Color

theorem digitOfColour_lt (c : Color) : digitOfColour c < 3 := by cases c <;> decide

theorem colourOfDigit_digitOfColour {c : Color} (hc : c ≠ 0) :
    colourOfDigit (digitOfColour c) = c := by
  cases c <;> first | rfl | exact absurd rfl hc

/-- The index of the first `M` colours. -/
def idxAux (et : List Color) (M : ℕ) : ℕ :=
  (List.range M).foldr (fun k acc => digitOfColour (et.getD k 0) * 3 ^ k + acc) 0

theorem idxAux_succ (et : List Color) (M : ℕ) :
    idxAux et (M + 1) = idxAux et M + digitOfColour (et.getD M 0) * 3 ^ M := by
  unfold idxAux
  rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero]
  have hfold : ∀ (l : List ℕ) (c : ℕ),
      l.foldr (fun k acc => digitOfColour (et.getD k 0) * 3 ^ k + acc) c =
      l.foldr (fun k acc => digitOfColour (et.getD k 0) * 3 ^ k + acc) 0 + c := by
    intro l c
    induction l with
    | nil => simp
    | cons x l ihl => rw [List.foldr_cons, List.foldr_cons, ihl]; ring
  rw [hfold]

theorem idxAux_lt (et : List Color) : ∀ M, idxAux et M < 3 ^ M := by
  intro M
  induction M with
  | zero => simp [idxAux]
  | succ M ih =>
    rw [idxAux_succ]
    have := digitOfColour_lt (et.getD M 0)
    have h3 : digitOfColour (et.getD M 0) * 3 ^ M ≤ 2 * 3 ^ M :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.pow_succ]
    omega

theorem digit_idxAux (et : List Color) : ∀ M k, k < M →
    digit k (idxAux et M) = digitOfColour (et.getD k 0) := by
  intro M
  induction M with
  | zero => intro k hk; omega
  | succ M ih =>
    intro k hk
    rw [idxAux_succ]
    have hlt := idxAux_lt et M
    by_cases hkM : k = M
    · subst hkM
      -- the new digit sits on top of a number below `3 ^ k`
      rw [Nat.add_comm, show digitOfColour (et.getD k 0) * 3 ^ k + idxAux et k
          = 0 * 3 ^ (k + 1) + digitOfColour (et.getD k 0) * 3 ^ k + idxAux et k by ring]
      exact digit_of_decomp (digitOfColour_lt _) hlt
    · have hk' : k < M := by omega
      rw [← ih k hk']
      -- adding a multiple of `3 ^ (k + 1)` leaves digit `k` alone
      obtain ⟨c, hc⟩ : 3 ^ (k + 1) ∣ 3 ^ M := Nat.pow_dvd_pow 3 (by omega)
      have hdec := decomp k (idxAux et M)
      have hlo := Nat.mod_lt (idxAux et M) (show 0 < 3 ^ k by positivity)
      conv_lhs => rw [hdec, hc]
      rw [show idxAux et M / 3 ^ (k + 1) * 3 ^ (k + 1) + digit k (idxAux et M) * 3 ^ k
            + idxAux et M % 3 ^ k + digitOfColour (et.getD M 0) * (3 ^ (k + 1) * c)
          = (idxAux et M / 3 ^ (k + 1) + digitOfColour (et.getD M 0) * c) * 3 ^ (k + 1)
            + digit k (idxAux et M) * 3 ^ k + idxAux et M % 3 ^ k by ring]
      exact digit_of_decomp (digit_lt _ _) hlo

theorem indexOf_eq_idxAux (m : ℕ) (et : List Color) : indexOf m et = idxAux et m := rfl

theorem indexOf_lt (m : ℕ) (et : List Color) : indexOf m et < 3 ^ m := idxAux_lt et m

/-- A zero-free list of length `m` is the digit list of its index. -/
theorem partialOf_indexOf {m : ℕ} {et : List Color} (hlen : et.length = m)
    (h0 : (0 : Color) ∉ et) : partialOf m (indexOf m et) = et := by
  apply List.ext_getElem
  · simp [hlen]
  · intro k hk1 hk2
    have hk : k < m := by simpa using hk1
    rw [getElem_partialOf m _ k hk, indexOf_eq_idxAux, digit_idxAux et m k hk]
    have hmem : et.getD k 0 ∈ et := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]
      exact List.getElem_mem _
    have hne : et.getD k 0 ≠ 0 := fun h => h0 (h ▸ hmem)
    rw [colourOfDigit_digitOfColour hne, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk2]
    rfl

end Bulk
end FourColor

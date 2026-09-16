import Mathlib.Algebra.Group.Even
import FourColor.CertFlip

/-!
# The chords of a chromogram

A chromogram matched by a trace is a non-crossing pairing of the trace's
non-`c1` positions: `push` opens a chord, `pop0`/`pop1` closes the most recently
opened one, and `skip` marks a position coloured `c1`, linked to nothing.  This
file makes that pairing explicit, as a list of `(push position, pop position)`
pairs produced by one scan with a stack of open positions, and proves the facts
a Kempe argument needs about *one* chord: the partner of a known position
exists, an even number of non-`c1` positions separate the two ends, and each of
the three flips supported by the chord — the chord alone, its interior, and
both — is accepted by `flipOk`, hence (by `matchg_flip`) still matches.

## Main definitions

* `chordsAux`, `chords` — the scan and its top-level form.
* `StackOk` — the invariant of the scan state.
* `ChordDisj`, `NonCrossing` — chords sharing no endpoint, and the non-crossing
  condition on a list of chords.

## Main results

* `chords_bounds`, `chords_disjoint`, `chords_nonCrossing`, `chords_endpoints`,
  `chords_endpoints_matchg` — the chord structure: the chords run forwards
  inside the word, no two share an endpoint, no two cross, and the endpoints are
  exactly the non-`skip` positions, that is the non-`c1` positions of the trace.
* `flipOk_of_chords` — a mask that is clear at every `skip` and constant on
  every chord passes `flipOk`.
* `chord_facts` — the one-chord package, for a chord given by both ends.
* `partner_exists` — the packaged one-chord statement, phrased for a caller that
  knows only one endpoint.
* `getD_flipFrom`, `length_flipFrom` — the pointwise reading of `flipFromB`.
-/

namespace FourColor

open Color

/-! ### Reading off a flipped trace -/

/-- Flipping a trace does not change its length. -/
@[simp] theorem length_flipFrom (M : ℕ) : ∀ (i : ℕ) (et : List Color),
    (flipFromB M i et).length = et.length := by
  intro i et
  induction et generalizing i with
  | nil => rfl
  | cons c cs ih => simp [flipFromB, ih]

/-- `flipFromB` acts pointwise: position `r` of the flipped trace is position `r`
of the trace, flipped when bit `i + r` of the mask is set. -/
theorem getD_flipFrom (M : ℕ) : ∀ (i : ℕ) (et : List Color) (r : ℕ),
    (flipFromB M i et).getD r 0
      = if r < et.length then flipC (M.testBit (i + r)) (et.getD r 0) else 0 := by
  intro i et
  induction et generalizing i with
  | nil => intro r; simp [flipFromB, List.getD]
  | cons c cs ih =>
    intro r
    cases r with
    | zero => simp [flipFromB]
    | succ r =>
      simp only [flipFromB, List.getD_cons_succ, List.length_cons, ih (i + 1) r]
      have : i + (r + 1) = i + 1 + r := by omega
      rw [this]
      by_cases h : r < cs.length
      · simp [h, Nat.succ_lt_succ h]
      · have h' : ¬ r + 1 < cs.length + 1 := by omega
        simp [h, h']

/-! ### The chord scan -/

/-- The chords of a chromogram: `(push position, pop position)` pairs, scanned
with a stack of the positions of the chords still open; `none` if a pop finds no
open chord, or if the word ends with a chord open. -/
def chordsAux : ℕ → List ℕ → Chromogram → Option (List (ℕ × ℕ))
  | _, [], [] => some []
  | _, _ :: _, [] => none
  | i, st, .skip :: w => chordsAux (i + 1) st w
  | i, st, .push :: w => chordsAux (i + 1) (i :: st) w
  | _, [], .pop0 :: _ => none
  | i, a :: st, .pop0 :: w => (chordsAux (i + 1) st w).map fun cs => (a, i) :: cs
  | _, [], .pop1 :: _ => none
  | i, a :: st, .pop1 :: w => (chordsAux (i + 1) st w).map fun cs => (a, i) :: cs

/-- The chords of a whole chromogram, scanned from position `0`. -/
def chords (w : Chromogram) : Option (List (ℕ × ℕ)) := chordsAux 0 [] w

@[simp] theorem chordsAux_nil_nil (i : ℕ) : chordsAux i [] [] = some [] := rfl

@[simp] theorem chordsAux_cons_nil (i a : ℕ) (st : List ℕ) :
    chordsAux i (a :: st) [] = none := rfl

@[simp] theorem chordsAux_skip (i : ℕ) (st : List ℕ) (w : Chromogram) :
    chordsAux i st (.skip :: w) = chordsAux (i + 1) st w := by cases st <;> rfl

@[simp] theorem chordsAux_push (i : ℕ) (st : List ℕ) (w : Chromogram) :
    chordsAux i st (.push :: w) = chordsAux (i + 1) (i :: st) w := by cases st <;> rfl

@[simp] theorem chordsAux_pop0_nil (i : ℕ) (w : Chromogram) :
    chordsAux i [] (.pop0 :: w) = none := rfl

@[simp] theorem chordsAux_pop1_nil (i : ℕ) (w : Chromogram) :
    chordsAux i [] (.pop1 :: w) = none := rfl

@[simp] theorem chordsAux_pop0_cons (i a : ℕ) (st : List ℕ) (w : Chromogram) :
    chordsAux i (a :: st) (.pop0 :: w)
      = (chordsAux (i + 1) st w).map fun cs => (a, i) :: cs := rfl

@[simp] theorem chordsAux_pop1_cons (i a : ℕ) (st : List ℕ) (w : Chromogram) :
    chordsAux i (a :: st) (.pop1 :: w)
      = (chordsAux (i + 1) st w).map fun cs => (a, i) :: cs := rfl

/-- The scan state is sound: the open positions lie below the current position
and were opened in increasing order. -/
def StackOk (i : ℕ) (st : List ℕ) : Prop := (∀ a ∈ st, a < i) ∧ st.Pairwise (· > ·)

/-- The empty stack is sound at any position. -/
theorem StackOk.nil (i : ℕ) : StackOk i [] := ⟨by simp, by simp⟩

/-- Reading a symbol that touches no chord keeps the stack sound. -/
theorem StackOk.succ {i : ℕ} {st : List ℕ} (h : StackOk i st) : StackOk (i + 1) st :=
  ⟨fun a ha => Nat.lt_succ_of_lt (h.1 a ha), h.2⟩

/-- Opening a chord at the current position keeps the stack sound. -/
theorem StackOk.push {i : ℕ} {st : List ℕ} (h : StackOk i st) :
    StackOk (i + 1) (i :: st) :=
  ⟨by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact Nat.lt_succ_of_lt (h.1 a ha),
   List.pairwise_cons.mpr ⟨fun a ha => h.1 a ha, h.2⟩⟩

/-- Closing the most recent chord keeps the stack sound. -/
theorem StackOk.tail {i a : ℕ} {st : List ℕ} (h : StackOk i (a :: st)) : StackOk i st :=
  ⟨fun b hb => h.1 b (List.mem_cons_of_mem _ hb), (List.pairwise_cons.mp h.2).2⟩

/-- Every chord found by the scan starts at an open position or at a position
the scan still has to read, and ends inside the part of the word being read. -/
theorem chordsAux_bounds : ∀ (w : Chromogram) (i : ℕ) (st : List ℕ) (cs : List (ℕ × ℕ)),
    StackOk i st → chordsAux i st w = some cs →
    ∀ ab ∈ cs, (ab.1 ∈ st ∨ i ≤ ab.1) ∧ ab.1 < ab.2 ∧ i ≤ ab.2 ∧ ab.2 < i + w.length := by
  intro w
  induction w with
  | nil =>
    intro i st cs _ h ab hab
    cases st with
    | nil => simp only [chordsAux_nil_nil, Option.some.injEq] at h; subst h; simp at hab
    | cons a st => simp at h
  | cons s w ih =>
    intro i st cs hst h ab hab
    cases s with
    | skip =>
      rw [chordsAux_skip] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) st cs hst.succ h ab hab
      refine ⟨?_, h2, by omega, by simp only [List.length_cons]; omega⟩
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by omega)
    | push =>
      rw [chordsAux_push] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (i :: st) cs hst.push h ab hab
      refine ⟨?_, h2, by omega, by simp only [List.length_cons]; omega⟩
      rcases h1 with h1 | h1
      · rcases List.mem_cons.mp h1 with h1 | h1
        · exact Or.inr (by omega)
        · exact Or.inl h1
      · exact Or.inr (by omega)
    | pop0 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop0_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        rcases List.mem_cons.mp hab with rfl | hab
        · exact ⟨Or.inl (List.mem_cons_self ..), hst.1 a (List.mem_cons_self ..),
            le_rfl, by simp only [List.length_cons]; omega⟩
        · obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) st cs' hst.tail.succ hcs' ab hab
          refine ⟨?_, h2, by omega, by simp only [List.length_cons]; omega⟩
          rcases h1 with h1 | h1
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr (by omega)
    | pop1 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop1_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        rcases List.mem_cons.mp hab with rfl | hab
        · exact ⟨Or.inl (List.mem_cons_self ..), hst.1 a (List.mem_cons_self ..),
            le_rfl, by simp only [List.length_cons]; omega⟩
        · obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) st cs' hst.tail.succ hcs' ab hab
          refine ⟨?_, h2, by omega, by simp only [List.length_cons]; omega⟩
          rcases h1 with h1 | h1
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr (by omega)

/-- Two chords share no endpoint. -/
def ChordDisj (ab cd : ℕ × ℕ) : Prop :=
  ab.1 ≠ cd.1 ∧ ab.1 ≠ cd.2 ∧ ab.2 ≠ cd.1 ∧ ab.2 ≠ cd.2

/-- Endpoint-disjointness is symmetric. -/
theorem ChordDisj.symm {ab cd : ℕ × ℕ} (h : ChordDisj ab cd) : ChordDisj cd ab :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

/-- The chords of a chromogram never cross: no chord starts inside another and
ends outside it. -/
def NonCrossing (cs : List (ℕ × ℕ)) : Prop :=
  ∀ ab ∈ cs, ∀ cd ∈ cs, ¬ (ab.1 < cd.1 ∧ cd.1 < ab.2 ∧ ab.2 < cd.2)


/-- A chord closed at the current position shares no endpoint with a chord found
later in the scan. -/
theorem chordDisj_head {w : Chromogram} {i a : ℕ} {st : List ℕ} {cs' : List (ℕ × ℕ)}
    (hst : StackOk i (a :: st)) (hcs' : chordsAux (i + 1) st w = some cs') :
    ∀ cd ∈ cs', ChordDisj (a, i) cd := by
  intro cd hcd
  obtain ⟨h1, _, h3, _⟩ := chordsAux_bounds w (i + 1) st cs' hst.tail.succ hcs' cd hcd
  have hai : a < i := hst.1 a (List.mem_cons_self ..)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change a ≠ cd.1
    rcases h1 with h1 | h1
    · have := (List.pairwise_cons.mp hst.2).1 cd.1 h1
      omega
    · omega
  · change a ≠ cd.2
    omega
  · change i ≠ cd.1
    rcases h1 with h1 | h1
    · have := hst.tail.1 cd.1 h1
      omega
    · omega
  · change i ≠ cd.2
    omega

/-- A chord closed at the current position crosses no chord found later. -/
theorem nonCrossing_head {w : Chromogram} {i a : ℕ} {st : List ℕ} {cs' : List (ℕ × ℕ)}
    (hst : StackOk i (a :: st)) (hcs' : chordsAux (i + 1) st w = some cs')
    (hnc : NonCrossing cs') : NonCrossing ((a, i) :: cs') := by
  have hai : a < i := hst.1 a (List.mem_cons_self ..)
  intro ab hab cd hcd
  rcases List.mem_cons.mp hab with rfl | hab <;> rcases List.mem_cons.mp hcd with rfl | hcd
  · change ¬ (a < a ∧ a < i ∧ i < i)
    omega
  · obtain ⟨h1, _, h3, _⟩ := chordsAux_bounds w (i + 1) st cs' hst.tail.succ hcs' cd hcd
    change ¬ (a < cd.1 ∧ cd.1 < i ∧ i < cd.2)
    rcases h1 with h1 | h1
    · have := (List.pairwise_cons.mp hst.2).1 cd.1 h1
      omega
    · omega
  · obtain ⟨_, _, h3, _⟩ := chordsAux_bounds w (i + 1) st cs' hst.tail.succ hcs' ab hab
    change ¬ (ab.1 < a ∧ a < ab.2 ∧ ab.2 < i)
    omega
  · exact hnc ab hab cd hcd

/-- Distinct chords of the scan are endpoint-disjoint: every position closes or
opens at most one chord. -/
theorem chordsAux_pairwise : ∀ (w : Chromogram) (i : ℕ) (st : List ℕ) (cs : List (ℕ × ℕ)),
    StackOk i st → chordsAux i st w = some cs → cs.Pairwise ChordDisj := by
  intro w
  induction w with
  | nil =>
    intro i st cs _ h
    cases st with
    | nil => simp only [chordsAux_nil_nil, Option.some.injEq] at h; subst h; simp
    | cons a st => simp at h
  | cons s w ih =>
    intro i st cs hst h
    cases s with
    | skip => exact ih (i + 1) st cs hst.succ (by rwa [chordsAux_skip] at h)
    | push => exact ih (i + 1) (i :: st) cs hst.push (by rwa [chordsAux_push] at h)
    | pop0 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop0_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        refine List.pairwise_cons.mpr ⟨?_, ih (i + 1) st cs' hst.tail.succ hcs'⟩
        intro cd hcd
        exact chordDisj_head hst hcs' cd hcd
    | pop1 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop1_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        refine List.pairwise_cons.mpr ⟨?_, ih (i + 1) st cs' hst.tail.succ hcs'⟩
        intro cd hcd
        exact chordDisj_head hst hcs' cd hcd

/-- The chords found by the scan are pairwise non-crossing. -/
theorem chordsAux_nonCrossing : ∀ (w : Chromogram) (i : ℕ) (st : List ℕ) (cs : List (ℕ × ℕ)),
    StackOk i st → chordsAux i st w = some cs → NonCrossing cs := by
  intro w
  induction w with
  | nil =>
    intro i st cs _ h
    cases st with
    | nil =>
      simp only [chordsAux_nil_nil, Option.some.injEq] at h
      subst h
      intro ab hab
      simp at hab
    | cons a st => simp at h
  | cons s w ih =>
    intro i st cs hst h
    cases s with
    | skip => exact ih (i + 1) st cs hst.succ (by rwa [chordsAux_skip] at h)
    | push => exact ih (i + 1) (i :: st) cs hst.push (by rwa [chordsAux_push] at h)
    | pop0 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop0_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        exact nonCrossing_head hst hcs' (ih (i + 1) st cs' hst.tail.succ hcs')
    | pop1 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop1_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        exact nonCrossing_head hst hcs' (ih (i + 1) st cs' hst.tail.succ hcs')

/-- The pop step of `chordsAux_cover`, shared by `pop0` and `pop1`. -/
theorem cover_pop {w : Chromogram} {i a : ℕ} {st : List ℕ} {cs' : List (ℕ × ℕ)}
    (s : GramSymbol) (hs : s ≠ .skip) (hst : StackOk i (a :: st))
    (ihS : ∀ x ∈ st, ∃ b, (x, b) ∈ cs')
    (ihC : ∀ k, k < w.length →
      ((∃ ab ∈ cs', ab.1 = i + 1 + k ∨ ab.2 = i + 1 + k) ↔ w.getD k .skip ≠ .skip)) :
    (∀ x ∈ a :: st, ∃ b, (x, b) ∈ (a, i) :: cs') ∧
    ∀ k, k < (s :: w).length →
      ((∃ ab ∈ (a, i) :: cs', ab.1 = i + k ∨ ab.2 = i + k)
        ↔ (s :: w).getD k .skip ≠ .skip) := by
  have hai : a < i := hst.1 a (List.mem_cons_self ..)
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨i, List.mem_cons_self ..⟩
    · obtain ⟨b, hb⟩ := ihS x hx
      exact ⟨b, List.mem_cons_of_mem _ hb⟩
  · intro k hk
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, ne_eq, Nat.add_zero]
      constructor
      · intro _; exact hs
      · intro _
        exact ⟨(a, i), List.mem_cons_self .., Or.inr rfl⟩
    | succ k =>
      have hk' : k < w.length := by simpa using Nat.lt_of_succ_lt_succ hk
      have hidx : i + (k + 1) = i + 1 + k := by omega
      rw [List.getD_cons_succ, hidx, ← ihC k hk']
      constructor
      · rintro ⟨ab, hab, hend⟩
        rcases List.mem_cons.mp hab with rfl | hab
        · exfalso
          rcases hend with hend | hend
          · have : a = i + 1 + k := hend
            omega
          · have : i = i + 1 + k := hend
            omega
        · exact ⟨ab, hab, hend⟩
      · rintro ⟨ab, hab, hend⟩
        exact ⟨ab, List.mem_cons_of_mem _ hab, hend⟩

/-- The scan pairs off exactly the non-`skip` positions: every open position is
eventually closed, and a position carries a chord end exactly when its symbol is
not `skip`. -/
theorem chordsAux_cover : ∀ (w : Chromogram) (i : ℕ) (st : List ℕ) (cs : List (ℕ × ℕ)),
    StackOk i st → chordsAux i st w = some cs →
    (∀ a ∈ st, ∃ b, (a, b) ∈ cs) ∧
    ∀ k, k < w.length →
      ((∃ ab ∈ cs, ab.1 = i + k ∨ ab.2 = i + k) ↔ w.getD k .skip ≠ .skip) := by
  intro w
  induction w with
  | nil =>
    intro i st cs _ h
    cases st with
    | nil =>
      simp only [chordsAux_nil_nil, Option.some.injEq] at h
      subst h
      exact ⟨by simp, by intro k hk; simp at hk⟩
    | cons a st => simp at h
  | cons s w ih =>
    intro i st cs hst h
    cases s with
    | skip =>
      rw [chordsAux_skip] at h
      obtain ⟨hS, hC⟩ := ih (i + 1) st cs hst.succ h
      refine ⟨hS, ?_⟩
      intro k hk
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, ne_eq, not_true_eq_false, iff_false, Nat.add_zero]
        rintro ⟨ab, hab, hend⟩
        obtain ⟨h1, _, h3, _⟩ := chordsAux_bounds w (i + 1) st cs hst.succ h ab hab
        rcases hend with hend | hend
        · rcases h1 with h1 | h1
          · have := hst.1 ab.1 h1
            omega
          · omega
        · omega
      | succ k =>
        have hk' : k < w.length := by simpa using Nat.lt_of_succ_lt_succ hk
        have hidx : i + (k + 1) = i + 1 + k := by omega
        rw [List.getD_cons_succ, hidx]
        exact hC k hk'
    | push =>
      rw [chordsAux_push] at h
      obtain ⟨hS, hC⟩ := ih (i + 1) (i :: st) cs hst.push h
      refine ⟨fun a ha => hS a (List.mem_cons_of_mem _ ha), ?_⟩
      intro k hk
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, ne_eq, Nat.add_zero]
        constructor
        · intro _; exact fun hcon => by cases hcon
        · intro _
          obtain ⟨b, hb⟩ := hS i (List.mem_cons_self ..)
          exact ⟨(i, b), hb, Or.inl rfl⟩
      | succ k =>
        have hk' : k < w.length := by simpa using Nat.lt_of_succ_lt_succ hk
        have hidx : i + (k + 1) = i + 1 + k := by omega
        rw [List.getD_cons_succ, hidx]
        exact hC k hk'
    | pop0 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop0_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        obtain ⟨hS, hC⟩ := ih (i + 1) st cs' hst.tail.succ hcs'
        exact cover_pop .pop0 (by simp) hst hS hC
    | pop1 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop1_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        obtain ⟨hS, hC⟩ := ih (i + 1) st cs' hst.tail.succ hcs'
        exact cover_pop .pop1 (by simp) hst hS hC

/-! ### The scan of a matched chromogram -/

/-- A matching step reads `skip` exactly at the colour `c1`. -/
theorem matchStep_skip_iff {e : Color} {s : GramSymbol} {lb lb' : List Bool}
    (h : matchStep e s lb = some lb') : s = .skip ↔ e = c1 := by
  cases e <;> cases s <;> rcases lb with _ | ⟨b, lb⟩ <;> (try cases b) <;>
    simp_all [matchStep]

/-- In a matched chromogram the `skip` positions are exactly the `c1` positions
of the trace. -/
theorem matchg_getD_skip_iff : ∀ (et : List Color) (w : Chromogram) (lb : List Bool),
    matchg lb et w = true → ∀ k, k < w.length →
      (w.getD k .skip = .skip ↔ et.getD k 0 = c1) := by
  intro et
  induction et with
  | nil =>
    intro w lb hm k hk
    cases w with
    | nil => simp at hk
    | cons s w => simp [matchg] at hm
  | cons e et ih =>
    intro w lb hm k hk
    cases w with
    | nil => simp at hm
    | cons s w =>
      rw [matchg_cons] at hm
      cases hstep : matchStep e s lb with
      | none => rw [hstep] at hm; simp at hm
      | some lb' =>
        rw [hstep] at hm
        simp only [Option.elim] at hm
        cases k with
        | zero =>
          simp only [List.getD_cons_zero]
          exact matchStep_skip_iff hstep
        | succ k =>
          simp only [List.getD_cons_succ]
          exact ih w lb' hm k (by simpa using Nat.lt_of_succ_lt_succ hk)

/-- A matched chromogram scans: every pop finds an open chord, and no chord is
left open at the end. -/
theorem chordsAux_isSome_of_matchg : ∀ (et : List Color) (w : Chromogram) (lb : List Bool)
    (st : List ℕ) (i : ℕ), matchg lb et w = true → lb.length = st.length →
      ∃ cs, chordsAux i st w = some cs := by
  intro et
  induction et with
  | nil =>
    intro w lb st i hm hlen
    cases w with
    | cons s w => simp [matchg] at hm
    | nil =>
      simp only [matchg_nil_nil, List.isEmpty_iff] at hm
      subst hm
      have hst : st = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst hst
      exact ⟨[], rfl⟩
  | cons e et ih =>
    intro w lb st i hm hlen
    cases w with
    | nil => simp at hm
    | cons s w =>
      rw [matchg_cons] at hm
      cases hstep : matchStep e s lb with
      | none => rw [hstep] at hm; simp at hm
      | some lb' =>
        rw [hstep] at hm
        simp only [Option.elim] at hm
        have hlen' := matchStep_length hstep
        cases s with
        | skip =>
          rw [chordsAux_skip]
          exact ih w lb' st (i + 1) hm (by rw [hlen']; simpa [cgramDepth] using hlen)
        | push =>
          rw [chordsAux_push]
          refine ih w lb' (i :: st) (i + 1) hm ?_
          rw [hlen']
          simp only [cgramDepth, List.length_cons, hlen]
        | pop0 =>
          obtain ⟨x, lb3, hlb⟩ := pop_stack .pop0 (Or.inl rfl) e lb lb' hstep
          subst hlb
          cases st with
          | nil => simp at hlen
          | cons a st =>
            rw [chordsAux_pop0_cons]
            have h1 : lb'.length = st.length := by
              simp only [cgramDepth, List.length_cons, Nat.add_sub_cancel] at hlen'
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨cs, hcs⟩ := ih w lb' st (i + 1) hm h1
            exact ⟨(a, i) :: cs, by rw [hcs]; rfl⟩
        | pop1 =>
          obtain ⟨x, lb3, hlb⟩ := pop_stack .pop1 (Or.inr rfl) e lb lb' hstep
          subst hlb
          cases st with
          | nil => simp at hlen
          | cons a st =>
            rw [chordsAux_pop1_cons]
            have h1 : lb'.length = st.length := by
              simp only [cgramDepth, List.length_cons, Nat.add_sub_cancel] at hlen'
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨cs, hcs⟩ := ih w lb' st (i + 1) hm h1
            exact ⟨(a, i) :: cs, by rw [hcs]; rfl⟩

/-! ### Flipping along the chords -/

/-- Generalised form of `flipOk_of_chords`: the flip-bit stack of `flipOk` is the
mask read along the stack of open positions. -/
theorem flipOk_of_chordsAux (M : ℕ) : ∀ (w : Chromogram) (i : ℕ) (st : List ℕ)
    (cs : List (ℕ × ℕ)), chordsAux i st w = some cs →
    (∀ k, k < w.length → w.getD k .skip = .skip → M.testBit (i + k) = false) →
    (∀ ab ∈ cs, M.testBit ab.1 = M.testBit ab.2) →
    flipOk M i (st.map fun a => M.testBit a) w = true := by
  intro w
  induction w with
  | nil =>
    intro i st cs h _ _
    cases st with
    | nil => simp [flipOk]
    | cons a st => simp at h
  | cons s w ih =>
    intro i st cs h hskip hchord
    cases s with
    | skip =>
      rw [chordsAux_skip] at h
      have h0 : M.testBit i = false := by
        have := hskip 0 (by simp) (by simp)
        simpa using this
      simp only [flipOk, h0, Bool.not_false, Bool.true_and]
      refine ih (i + 1) st cs h (fun k hk hs => ?_) hchord
      have := hskip (k + 1) (by simpa using Nat.succ_lt_succ hk) (by simpa using hs)
      have hidx : i + (k + 1) = i + 1 + k := by omega
      rwa [hidx] at this
    | push =>
      rw [chordsAux_push] at h
      simp only [flipOk]
      have := ih (i + 1) (i :: st) cs h (fun k hk hs => ?_) hchord
      · simpa using this
      · have := hskip (k + 1) (by simpa using Nat.succ_lt_succ hk) (by simpa using hs)
        have hidx : i + (k + 1) = i + 1 + k := by omega
        rwa [hidx] at this
    | pop0 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop0_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        have hb : M.testBit a = M.testBit i := hchord (a, i) (List.mem_cons_self ..)
        simp only [List.map_cons, flipOk, hb, beq_self_eq_true, Bool.true_and]
        refine ih (i + 1) st cs' hcs' (fun k hk hs => ?_)
          (fun ab hab => hchord ab (List.mem_cons_of_mem _ hab))
        have := hskip (k + 1) (by simpa using Nat.succ_lt_succ hk) (by simpa using hs)
        have hidx : i + (k + 1) = i + 1 + k := by omega
        rwa [hidx] at this
    | pop1 =>
      cases st with
      | nil => simp at h
      | cons a st =>
        rw [chordsAux_pop1_cons, Option.map_eq_some_iff] at h
        obtain ⟨cs', hcs', rfl⟩ := h
        have hb : M.testBit a = M.testBit i := hchord (a, i) (List.mem_cons_self ..)
        simp only [List.map_cons, flipOk, hb, beq_self_eq_true, Bool.true_and]
        refine ih (i + 1) st cs' hcs' (fun k hk hs => ?_)
          (fun ab hab => hchord ab (List.mem_cons_of_mem _ hab))
        have := hskip (k + 1) (by simpa using Nat.succ_lt_succ hk) (by simpa using hs)
        have hidx : i + (k + 1) = i + 1 + k := by omega
        rwa [hidx] at this

/-- **A mask clear at every `skip` and constant on every chord passes `flipOk`.**
Together with `matchg_flip` this says the flipped trace still matches. -/
theorem flipOk_of_chords {M : ℕ} {w : Chromogram} {cs : List (ℕ × ℕ)}
    (hcs : chords w = some cs)
    (hskip : ∀ k, k < w.length → w.getD k .skip = .skip → M.testBit k = false)
    (hchord : ∀ ab ∈ cs, M.testBit ab.1 = M.testBit ab.2) :
    flipOk M 0 [] w = true := by
  have := flipOk_of_chordsAux M w 0 [] cs hcs (by simpa using hskip) hchord
  simpa using this

/-! ### One chord -/

/-- A symmetric pairwise relation holds between any two distinct members. -/
theorem pairwise_forall_of_symm {α : Type*} {R : α → α → Prop} (hsymm : ∀ x y, R x y → R y x) :
    ∀ {l : List α}, l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons z l ih =>
    intro h x hx y hy hxy
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp h
    rw [List.mem_cons] at hx hy
    rcases hx with hx1 | hx1
    · rcases hy with hy1 | hy1
      · exact absurd (hx1.trans hy1.symm) hxy
      · subst hx1
        exact h1 y hy1
    · rcases hy with hy1 | hy1
      · subst hy1
        exact hsymm _ _ (h1 x hx1)
      · exact ih h2 x hx1 y hy1 hxy

/-- A mask described by a predicate takes equal values at equivalent positions. -/
theorem testBit_eq_of_iff {M x y : ℕ} {P : ℕ → Prop} (h : ∀ r, M.testBit r = true ↔ P r)
    (hxy : P x ↔ P y) : M.testBit x = M.testBit y := by
  cases hx : M.testBit x <;> cases hy : M.testBit y
  · rfl
  · exact absurd ((h x).2 (hxy.2 ((h y).1 hy))) (by simp [hx])
  · exact absurd ((h y).2 (hxy.1 ((h x).1 hx))) (by simp [hy])
  · rfl

/-- A mask described by a predicate is clear where the predicate fails. -/
theorem testBit_eq_false_of_not {M r : ℕ} {P : ℕ → Prop} (h : ∀ r, M.testBit r = true ↔ P r)
    (hr : ¬ P r) : M.testBit r = false := by
  cases hb : M.testBit r
  · rfl
  · exact absurd ((h r).1 hb) hr

/-- Listing both ends of each chord doubles the count. -/
theorem length_flatMap_pair (l : List (ℕ × ℕ)) :
    (l.flatMap fun cd => [cd.1, cd.2]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons cd l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

/-! ### The chord structure, packaged -/

/-- A chromogram matched by a trace has a chord list. -/
theorem chords_isSome_of_matchg {et : List Color} {w : Chromogram}
    (hm : matchg [] et w = true) : ∃ cs, chords w = some cs :=
  chordsAux_isSome_of_matchg et w [] [] 0 hm rfl

/-- Every chord runs forwards and stays inside the word. -/
theorem chords_bounds {w : Chromogram} {cs : List (ℕ × ℕ)} (hcs : chords w = some cs) :
    ∀ ab ∈ cs, ab.1 < ab.2 ∧ ab.2 < w.length := by
  intro ab hab
  obtain ⟨-, h2, -, h4⟩ := chordsAux_bounds w 0 [] cs (StackOk.nil 0) hcs ab hab
  exact ⟨h2, by omega⟩

/-- Distinct chords share no endpoint: a position is an end of at most one chord. -/
theorem chords_disjoint {w : Chromogram} {cs : List (ℕ × ℕ)} (hcs : chords w = some cs) :
    ∀ ab ∈ cs, ∀ cd ∈ cs, ab ≠ cd → ChordDisj ab cd :=
  fun ab hab cd hcd hne =>
    pairwise_forall_of_symm (fun _ _ h => ChordDisj.symm h)
      (chordsAux_pairwise w 0 [] cs (StackOk.nil 0) hcs) ab hab cd hcd hne

/-- The chords of a chromogram do not cross. -/
theorem chords_nonCrossing {w : Chromogram} {cs : List (ℕ × ℕ)} (hcs : chords w = some cs) :
    NonCrossing cs :=
  chordsAux_nonCrossing w 0 [] cs (StackOk.nil 0) hcs

/-- The chord endpoints are exactly the non-`skip` positions of the word. -/
theorem chords_endpoints {w : Chromogram} {cs : List (ℕ × ℕ)} (hcs : chords w = some cs) :
    ∀ r, r < w.length → ((∃ ab ∈ cs, ab.1 = r ∨ ab.2 = r) ↔ w.getD r .skip ≠ .skip) := by
  intro r hr
  have h := (chordsAux_cover w 0 [] cs (StackOk.nil 0) hcs).2 r hr
  simpa using h

/-- The chord endpoints are exactly the non-`c1` positions of a matching trace. -/
theorem chords_endpoints_matchg {et : List Color} {w : Chromogram}
    (hm : matchg [] et w = true) {cs : List (ℕ × ℕ)} (hcs : chords w = some cs) :
    ∀ r, r < et.length → ((∃ ab ∈ cs, ab.1 = r ∨ ab.2 = r) ↔ et.getD r 0 ≠ c1) := by
  have hlen : w.length = et.length := matchg_length et [] w hm
  intro r hr
  exact (chords_endpoints hcs r (by omega)).trans
    (not_congr (matchg_getD_skip_iff et w [] hm r (by omega)))

/-- **The facts about one chord.**  For a chord `(a, b)` of a matched
chromogram: both ends are non-`c1` positions of the trace, an even number of
non-`c1` positions lie strictly between them, and the mask flipping the chord
alone, its interior, or both is accepted by `flipOk`. -/
theorem chord_facts {et : List Color} {w : Chromogram} (hm : matchg [] et w = true)
    {cs : List (ℕ × ℕ)} (hcs : chords w = some cs) {a b : ℕ} (hab : (a, b) ∈ cs) :
    a < b ∧ b < et.length ∧ et.getD a 0 ≠ c1 ∧ et.getD b 0 ≠ c1 ∧
    Even (((List.range et.length).filter
      fun r => a < r ∧ r < b ∧ et.getD r 0 ≠ c1).length) ∧
    (∀ M : ℕ, (∀ r, M.testBit r = true ↔ (r = a ∨ r = b)) → flipOk M 0 [] w = true) ∧
    (∀ M : ℕ, (∀ r, M.testBit r = true ↔ (a < r ∧ r < b ∧ et.getD r 0 ≠ c1)) →
      flipOk M 0 [] w = true) ∧
    (∀ M : ℕ, (∀ r, M.testBit r = true ↔
        (r = a ∨ r = b ∨ (a < r ∧ r < b ∧ et.getD r 0 ≠ c1))) → flipOk M 0 [] w = true) := by
  have hcs' : chordsAux 0 [] w = some cs := hcs
  have hlen : w.length = et.length := matchg_length et [] w hm
  have hbnd : ∀ cd ∈ cs, cd.1 < cd.2 ∧ cd.2 < et.length := by
    intro cd hcd
    obtain ⟨-, h2, -, h4⟩ := chordsAux_bounds w 0 [] cs (StackOk.nil 0) hcs' cd hcd
    exact ⟨h2, by omega⟩
  have hpw := chordsAux_pairwise w 0 [] cs (StackOk.nil 0) hcs'
  have hnc := chordsAux_nonCrossing w 0 [] cs (StackOk.nil 0) hcs'
  obtain ⟨-, hcov⟩ := chordsAux_cover w 0 [] cs (StackOk.nil 0) hcs'
  have hsk : ∀ r, r < et.length → (w.getD r .skip = .skip ↔ et.getD r 0 = c1) :=
    fun r hr => matchg_getD_skip_iff et w [] hm r (by omega)
  have hend : ∀ r, r < et.length → ((∃ cd ∈ cs, cd.1 = r ∨ cd.2 = r) ↔ et.getD r 0 ≠ c1) := by
    intro r hr
    have h1 := hcov r (by omega)
    simp only [Nat.zero_add] at h1
    exact h1.trans (not_congr (hsk r hr))
  obtain ⟨hab12, hab2⟩ := hbnd (a, b) hab
  have hab12 : a < b := hab12
  have hca : et.getD a 0 ≠ c1 := (hend a (by omega)).1 ⟨(a, b), hab, Or.inl rfl⟩
  have hcb : et.getD b 0 ≠ c1 := (hend b (by omega)).1 ⟨(a, b), hab, Or.inr rfl⟩
  -- endpoints of the other chords avoid both ends of `(a, b)`
  have hdisj : ∀ cd ∈ cs, cd ≠ (a, b) →
      a ≠ cd.1 ∧ a ≠ cd.2 ∧ b ≠ cd.1 ∧ b ≠ cd.2 := by
    intro cd hcd hne
    exact pairwise_forall_of_symm (fun _ _ h => ChordDisj.symm h) hpw (a, b) hab cd hcd
      (Ne.symm hne)
  -- by non-crossing, a chord has either both ends inside `(a, b)` or neither
  have hnest : ∀ cd ∈ cs, ((a < cd.1 ∧ cd.1 < b) ↔ (a < cd.2 ∧ cd.2 < b)) := by
    intro cd hcd
    obtain ⟨he1, he2⟩ := hbnd cd hcd
    by_cases hcase : cd = (a, b)
    · subst hcase
      change (a < a ∧ a < b) ↔ (a < b ∧ b < b)
      omega
    · obtain ⟨e1, e2, e3, e4⟩ := hdisj cd hcd hcase
      constructor
      · rintro ⟨g1, g2⟩
        refine ⟨by omega, ?_⟩
        by_contra hcon
        exact hnc (a, b) hab cd hcd ⟨g1, g2, by omega⟩
      · rintro ⟨g1, g2⟩
        refine ⟨?_, by omega⟩
        by_contra hcon
        exact hnc cd hcd (a, b) hab ⟨by omega, by omega, by omega⟩
  -- the flip criterion, for a mask described by a predicate
  have hflip : ∀ (M : ℕ) (P : ℕ → Prop), (∀ r, M.testBit r = true ↔ P r) →
      (∀ r, r < et.length → et.getD r 0 = c1 → ¬ P r) →
      (∀ cd ∈ cs, (P cd.1 ↔ P cd.2)) → flipOk M 0 [] w = true := by
    intro M P hP hskip hchord
    refine flipOk_of_chords hcs (fun k hk hks => ?_) (fun cd hcd => ?_)
    · exact testBit_eq_false_of_not hP (hskip k (by omega) ((hsk k (by omega)).1 hks))
    · exact testBit_eq_of_iff hP (hchord cd hcd)
  -- the interior colours of the other chords
  have hcend : ∀ cd ∈ cs, et.getD cd.1 0 ≠ c1 ∧ et.getD cd.2 0 ≠ c1 := by
    intro cd hcd
    obtain ⟨he1, he2⟩ := hbnd cd hcd
    exact ⟨(hend cd.1 (by omega)).1 ⟨cd, hcd, Or.inl rfl⟩,
      (hend cd.2 (by omega)).1 ⟨cd, hcd, Or.inr rfl⟩⟩
  refine ⟨hab12, hab2, hca, hcb, ?_, ?_, ?_, ?_⟩
  · -- evenness of the interior count
    have hmem : ∀ r, r ∈ (List.range et.length).filter
          (fun r => a < r ∧ r < b ∧ et.getD r 0 ≠ c1) ↔
        r ∈ (cs.filter fun cd => a < cd.1 ∧ cd.2 < b).flatMap fun cd => [cd.1, cd.2] := by
      intro r
      simp only [List.mem_filter, List.mem_range, List.mem_flatMap, decide_eq_true_eq,
        List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨hr, ha, hb', hcr⟩
        obtain ⟨cd, hcd, hcdr⟩ := (hend r hr).2 hcr
        have hn := hnest cd hcd
        obtain ⟨he1, he2⟩ := hbnd cd hcd
        rcases hcdr with h | h
        · have h1 : a < cd.1 ∧ cd.1 < b := by omega
          have h2 := hn.1 h1
          exact ⟨cd, ⟨hcd, h1.1, h2.2⟩, Or.inl h.symm⟩
        · have h2 : a < cd.2 ∧ cd.2 < b := by omega
          have h1 := hn.2 h2
          exact ⟨cd, ⟨hcd, h1.1, h2.2⟩, Or.inr h.symm⟩
      · rintro ⟨cd, ⟨hcd, hi1, hi2⟩, hr⟩
        obtain ⟨he1, he2⟩ := hbnd cd hcd
        obtain ⟨hc1, hc2⟩ := hcend cd hcd
        rcases hr with rfl | rfl
        · exact ⟨by omega, by omega, by omega, hc1⟩
        · exact ⟨by omega, by omega, by omega, hc2⟩
    have hnodupS : ((List.range et.length).filter
        (fun r => a < r ∧ r < b ∧ et.getD r 0 ≠ c1)).Nodup := List.nodup_range.filter _
    have hnodupE : ((cs.filter fun cd => a < cd.1 ∧ cd.2 < b).flatMap
        fun cd => [cd.1, cd.2]).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun cd hcd => ?_, ?_⟩
      · have h12 := (hbnd cd (List.mem_of_mem_filter hcd)).1
        have hne : cd.1 ≠ cd.2 := by omega
        simp [hne]
      · refine List.Pairwise.imp ?_ (hpw.filter _)
        intro cd cd' h z hz hz'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hz'
        obtain ⟨d1, d2, d3, d4⟩ := h
        have e1 : cd.1 ≠ cd'.1 := d1
        have e2 : cd.1 ≠ cd'.2 := d2
        have e3 : cd.2 ≠ cd'.1 := d3
        have e4 : cd.2 ≠ cd'.2 := d4
        omega
    have hle := Nat.le_antisymm (hnodupS.length_le_of_subset fun x hx => (hmem x).1 hx)
      (hnodupE.length_le_of_subset fun x hx => (hmem x).2 hx)
    exact ⟨(cs.filter fun cd => a < cd.1 ∧ cd.2 < b).length, by
      rw [hle, length_flatMap_pair]; omega⟩
  · -- the chord alone
    intro M hM
    refine hflip M _ hM (fun r hr hcr => ?_) (fun cd hcd => ?_)
    · rintro (rfl | rfl)
      · exact hca hcr
      · exact hcb hcr
    · by_cases hcase : cd = (a, b)
      · subst hcase
        change (a = a ∨ a = b) ↔ (b = a ∨ b = b)
        omega
      · obtain ⟨e1, e2, e3, e4⟩ := hdisj cd hcd hcase
        omega
  · -- the interior
    intro M hM
    refine hflip M _ hM (fun r hr hcr => ?_) (fun cd hcd => ?_)
    · rintro ⟨-, -, h3⟩
      exact h3 hcr
    · obtain ⟨hc1, hc2⟩ := hcend cd hcd
      have hn := hnest cd hcd
      constructor
      · rintro ⟨g1, g2, -⟩
        exact ⟨(hn.1 ⟨g1, g2⟩).1, (hn.1 ⟨g1, g2⟩).2, hc2⟩
      · rintro ⟨g1, g2, -⟩
        exact ⟨(hn.2 ⟨g1, g2⟩).1, (hn.2 ⟨g1, g2⟩).2, hc1⟩
  · -- the chord and its interior
    intro M hM
    refine hflip M _ hM (fun r hr hcr => ?_) (fun cd hcd => ?_)
    · rintro (rfl | rfl | ⟨-, -, h3⟩)
      · exact hca hcr
      · exact hcb hcr
      · exact h3 hcr
    · obtain ⟨hc1, hc2⟩ := hcend cd hcd
      have hn := hnest cd hcd
      by_cases hcase : cd = (a, b)
      · subst hcase
        change (a = a ∨ _) ↔ (b = a ∨ b = b ∨ _)
        exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => Or.inl rfl⟩
      · obtain ⟨e1, e2, e3, e4⟩ := hdisj cd hcd hcase
        constructor
        · rintro (h | h | ⟨g1, g2, -⟩)
          · omega
          · omega
          · exact Or.inr (Or.inr ⟨(hn.1 ⟨g1, g2⟩).1, (hn.1 ⟨g1, g2⟩).2, hc2⟩)
        · rintro (h | h | ⟨g1, g2, -⟩)
          · omega
          · omega
          · exact Or.inr (Or.inr ⟨(hn.2 ⟨g1, g2⟩).1, (hn.2 ⟨g1, g2⟩).2, hc1⟩)

/-- **The partner of a known position.**  In a trace matching a chromogram,
every non-`c1` position `p` is linked by a chord to a second non-`c1` position
`q`: an even number of non-`c1` positions lie strictly between them, and each of
the three flips the chord supports — the chord alone, the positions strictly
inside it, and both — passes `flipOk`, hence by `matchg_flip` still matches the
chromogram. -/
theorem partner_exists {et : List Color} {w : Chromogram} (hm : matchg [] et w = true)
    {p : ℕ} (hp : p < et.length) (hc : et.getD p 0 ≠ c1) :
    ∃ q, q < et.length ∧ q ≠ p ∧ et.getD q 0 ≠ c1 ∧
      Even (((List.range et.length).filter
        fun r => min p q < r ∧ r < max p q ∧ et.getD r 0 ≠ c1).length) ∧
      (∀ M : ℕ, (∀ r, M.testBit r = true ↔ (r = p ∨ r = q)) → flipOk M 0 [] w = true) ∧
      (∀ M : ℕ, (∀ r, M.testBit r = true ↔
          (min p q < r ∧ r < max p q ∧ et.getD r 0 ≠ c1)) → flipOk M 0 [] w = true) ∧
      (∀ M : ℕ, (∀ r, M.testBit r = true ↔
          (r = p ∨ r = q ∨ (min p q < r ∧ r < max p q ∧ et.getD r 0 ≠ c1))) →
        flipOk M 0 [] w = true) := by
  have hlen : w.length = et.length := matchg_length et [] w hm
  obtain ⟨cs, hcs⟩ := chordsAux_isSome_of_matchg et w [] [] 0 hm rfl
  have hcs' : chords w = some cs := hcs
  obtain ⟨-, hcov⟩ := chordsAux_cover w 0 [] cs (StackOk.nil 0) hcs
  have hsk := matchg_getD_skip_iff et w [] hm p (by omega)
  have hpe : ∃ cd ∈ cs, cd.1 = p ∨ cd.2 = p := by
    have h1 := hcov p (by omega)
    simp only [Nat.zero_add] at h1
    exact h1.2 fun hcon => hc (hsk.1 hcon)
  obtain ⟨cd, hcd, hp'⟩ := hpe
  have hab : (cd.1, cd.2) ∈ cs := by simpa using hcd
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := chord_facts hm hcs' hab
  rcases hp' with h | h
  · subst h
    have hmin : min cd.1 cd.2 = cd.1 := by omega
    have hmax : max cd.1 cd.2 = cd.2 := by omega
    refine ⟨cd.2, by omega, by omega, h4, ?_, h6, ?_, ?_⟩
    · rw [hmin, hmax]
      exact h5
    · rw [hmin, hmax]
      exact h7
    · rw [hmin, hmax]
      exact h8
  · subst h
    have hmin : min cd.2 cd.1 = cd.1 := by omega
    have hmax : max cd.2 cd.1 = cd.2 := by omega
    refine ⟨cd.1, by omega, by omega, h3, ?_, ?_, ?_, ?_⟩
    · rw [hmin, hmax]
      exact h5
    · intro M hM
      exact h6 M fun r => (hM r).trans (by tauto)
    · rw [hmin, hmax]
      exact h7
    · rw [hmin, hmax]
      intro M hM
      exact h8 M fun r => (hM r).trans (by tauto)

end FourColor

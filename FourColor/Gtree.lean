import FourColor.Chromogram

/-!
# Chromogram trees

Sets of partial chromograms are stored as four-way trees, much as partial edge
traces are stored in `Ctree`s.  Unlike colouring trees, gram trees never record
multiplicities, so only a membership function is needed; counting matches is
defined from the characteristic function alone.

The eight leaf constructors denote the small sets of single symbols that
actually arise: `leaf0`–`leaf3` for one symbol and `leaf01`, `leaf12`, `leaf13`,
`leaf23` for two, indexed in the order `push`, `skip`, `pop0`, `pop1`.

## Main definitions

* `Gtree`, `Gtree.mem` — the trees and their membership.
* `hasMatch`, `matchCount` — existence and counting of matching chromograms for
  an arbitrary specification; `Gtree.sub` instantiates the latter at a tree.
* `Gtree.empty4`, `Gtree.consPairs` — the machinery of the restriction
  operation, which splits a tree into a partitioning pair.

## References

Gonthier's `theories/proof/gtree.v`.
-/

namespace FourColor

open Color

/-- A chromogram tree. -/
inductive Gtree
  /-- A node; the subtrees follow `push`, `skip`, `pop0`, `pop1` respectively. -/
  | node (t₀ t₁ t₂ t₃ : Gtree)
  /-- The one-symbol leaf for `push`. -/
  | leaf0
  /-- The one-symbol leaf for `skip`. -/
  | leaf1
  /-- The one-symbol leaf for `pop0`. -/
  | leaf2
  /-- The one-symbol leaf for `pop1`. -/
  | leaf3
  /-- The leaf for `push` or `skip`. -/
  | leaf01
  /-- The leaf for `skip` or `pop0`. -/
  | leaf12
  /-- The leaf for `skip` or `pop1`. -/
  | leaf13
  /-- The leaf for `pop0` or `pop1`. -/
  | leaf23
  /-- The empty tree. -/
  | empty
  deriving DecidableEq, Repr, Inhabited

namespace Gtree

def isEmpty : Gtree → Bool
  | .empty => true
  | _ => false

/-- The subtree following a symbol. -/
def sel : Gtree → GramSymbol → Gtree
  | .node t₀ t₁ t₂ t₃, s => match s with
    | .push => t₀
    | .skip => t₁
    | .pop0 => t₂
    | .pop1 => t₃
  | _, _ => .empty

/-- Which single symbols a leaf contains. -/
def leafMem : Gtree → GramSymbol → Bool
  | .leaf0, .push => true
  | .leaf1, .skip => true
  | .leaf2, .pop0 => true
  | .leaf3, .pop1 => true
  | .leaf01, .push => true
  | .leaf01, .skip => true
  | .leaf12, .skip => true
  | .leaf12, .pop0 => true
  | .leaf13, .skip => true
  | .leaf13, .pop1 => true
  | .leaf23, .pop0 => true
  | .leaf23, .pop1 => true
  | _, _ => false

/-- `t` contains the partial chromogram `w`. -/
def mem : Gtree → Chromogram → Bool
  | _, [] => false
  | .node t₀ t₁ t₂ t₃, s :: w => mem (sel (.node t₀ t₁ t₂ t₃) s) w
  | t, [s] => leafMem t s
  | _, _ :: _ :: _ => false

@[simp] theorem isEmpty_eq_true {t : Gtree} : isEmpty t = true ↔ t = .empty := by
  cases t <;> simp [isEmpty]

@[simp] theorem sel_node_push (t₀ t₁ t₂ t₃ : Gtree) :
    sel (.node t₀ t₁ t₂ t₃) .push = t₀ := rfl

@[simp] theorem sel_node_skip (t₀ t₁ t₂ t₃ : Gtree) :
    sel (.node t₀ t₁ t₂ t₃) .skip = t₁ := rfl

@[simp] theorem sel_node_pop0 (t₀ t₁ t₂ t₃ : Gtree) :
    sel (.node t₀ t₁ t₂ t₃) .pop0 = t₂ := rfl

@[simp] theorem sel_node_pop1 (t₀ t₁ t₂ t₃ : Gtree) :
    sel (.node t₀ t₁ t₂ t₃) .pop1 = t₃ := rfl

@[simp] theorem mem_nil (t : Gtree) : mem t [] = false := by cases t <;> rfl

@[simp] theorem mem_empty (w : Chromogram) : mem .empty w = false := by
  cases w with
  | nil => rfl
  | cons s w => cases w <;> rfl

@[simp] theorem mem_node_cons (t₀ t₁ t₂ t₃ : Gtree) (s : GramSymbol) (w : Chromogram) :
    mem (.node t₀ t₁ t₂ t₃) (s :: w) = mem (sel (.node t₀ t₁ t₂ t₃) s) w := rfl

end Gtree

/-! ### Matching against an arbitrary specification -/

/-- `hasMatch bs ct w`: some partial trace satisfying `ct` matches `w` in the
open-chord context `bs`. -/
def hasMatch : List Bool → (List Color → Bool) → Chromogram → Bool
  | _, ct, [] => ct []
  | bs, ct, .push :: w =>
      hasMatch (false :: bs) (fun et => ct (c2 :: et)) w ||
      hasMatch (true :: bs) (fun et => ct (c3 :: et)) w
  | bs, ct, .skip :: w => hasMatch bs (fun et => ct (c1 :: et)) w
  | [], _, .pop0 :: _ => false
  | false :: bs, ct, .pop0 :: w => hasMatch bs (fun et => ct (c2 :: et)) w
  | true :: bs, ct, .pop0 :: w => hasMatch bs (fun et => ct (c3 :: et)) w
  | [], _, .pop1 :: _ => false
  | false :: bs, ct, .pop1 :: w => hasMatch bs (fun et => ct (c3 :: et)) w
  | true :: bs, ct, .pop1 :: w => hasMatch bs (fun et => ct (c2 :: et)) w

theorem hasMatch_iff : ∀ (w : Chromogram) (bs : List Bool) (ct : List Color → Bool),
    hasMatch bs ct w = true ↔ ∃ et, ct et = true ∧ matchpg bs et w = true := by
  intro w
  induction w with
  | nil =>
    intro bs ct
    constructor
    · intro h; exact ⟨[], h, rfl⟩
    · rintro ⟨et, hct, hm⟩
      cases et with
      | nil => exact hct
      | cons e et => simp at hm
  | cons s w ih =>
    intro bs ct
    cases s with
    | push =>
      rw [hasMatch, Bool.or_eq_true, ih, ih]
      constructor
      · rintro (⟨et, hct, hm⟩ | ⟨et, hct, hm⟩)
        · exact ⟨c2 :: et, hct, by simpa [matchStep] using hm⟩
        · exact ⟨c3 :: et, hct, by simpa [matchStep] using hm⟩
      · rintro ⟨et, hct, hm⟩
        cases et with
        | nil => simp at hm
        | cons e et =>
          cases e <;> simp only [matchpg_cons, matchStep, Option.elim] at hm
          · exact absurd hm (by simp)
          · exact absurd hm (by simp)
          · exact Or.inl ⟨et, hct, hm⟩
          · exact Or.inr ⟨et, hct, hm⟩
    | skip =>
      rw [hasMatch, ih]
      constructor
      · rintro ⟨et, hct, hm⟩
        exact ⟨c1 :: et, hct, by simpa [matchStep] using hm⟩
      · rintro ⟨et, hct, hm⟩
        cases et with
        | nil => simp at hm
        | cons e et =>
          cases e <;> simp only [matchpg_cons, matchStep, Option.elim] at hm
          · exact absurd hm (by simp)
          · exact ⟨et, hct, hm⟩
          · exact absurd hm (by simp)
          · exact absurd hm (by simp)
    | pop0 =>
      rcases bs with _ | ⟨b, bs⟩
      · simp only [hasMatch, Bool.false_eq_true, false_iff]
        rintro ⟨et, _, hm⟩
        cases et with
        | nil => simp at hm
        | cons e et => cases e <;> simp [matchStep] at hm
      · cases b <;> rw [hasMatch, ih] <;>
          constructor
        · rintro ⟨et, hct, hm⟩
          exact ⟨c2 :: et, hct, by simpa [matchStep] using hm⟩
        · rintro ⟨et, hct, hm⟩
          cases et with
          | nil => simp at hm
          | cons e et =>
            cases e <;> simp only [matchpg_cons, matchStep, Option.elim] at hm <;>
              first | exact ⟨et, hct, hm⟩ | simp at hm
        · rintro ⟨et, hct, hm⟩
          exact ⟨c3 :: et, hct, by simpa [matchStep] using hm⟩
        · rintro ⟨et, hct, hm⟩
          cases et with
          | nil => simp at hm
          | cons e et =>
            cases e <;> simp only [matchpg_cons, matchStep, Option.elim] at hm <;>
              first | exact ⟨et, hct, hm⟩ | simp at hm
    | pop1 =>
      rcases bs with _ | ⟨b, bs⟩
      · simp only [hasMatch, Bool.false_eq_true, false_iff]
        rintro ⟨et, _, hm⟩
        cases et with
        | nil => simp at hm
        | cons e et => cases e <;> simp [matchStep] at hm
      · cases b <;> rw [hasMatch, ih] <;>
          constructor
        · rintro ⟨et, hct, hm⟩
          exact ⟨c3 :: et, hct, by simpa [matchStep] using hm⟩
        · rintro ⟨et, hct, hm⟩
          cases et with
          | nil => simp at hm
          | cons e et =>
            cases e <;> simp only [matchpg_cons, matchStep, Option.elim] at hm <;>
              first | exact ⟨et, hct, hm⟩ | simp at hm
        · rintro ⟨et, hct, hm⟩
          exact ⟨c2 :: et, hct, by simpa [matchStep] using hm⟩
        · rintro ⟨et, hct, hm⟩
          cases et with
          | nil => simp at hm
          | cons e et =>
            cases e <;> simp only [matchpg_cons, matchStep, Option.elim] at hm <;>
              first | exact ⟨et, hct, hm⟩ | simp at hm

/-! ### Counting matches -/

/-- The number of partial chromograms satisfying `st` that match `et` in the
open-chord context `bs`. -/
def matchCount : (Chromogram → Bool) → List Bool → List Color → ℕ
  | st, _, [] => if st [] then 1 else 0
  | _, _, .c0 :: _ => 0
  | st, bs, .c1 :: et => matchCount (fun w => st (.skip :: w)) bs et
  | st, bs, .c2 :: et =>
      matchCount (fun w => st (.push :: w)) (false :: bs) et +
        (match bs with
         | [] => 0
         | false :: bs' => matchCount (fun w => st (.pop0 :: w)) bs' et
         | true :: bs' => matchCount (fun w => st (.pop1 :: w)) bs' et)
  | st, bs, .c3 :: et =>
      matchCount (fun w => st (.push :: w)) (true :: bs) et +
        (match bs with
         | [] => 0
         | false :: bs' => matchCount (fun w => st (.pop1 :: w)) bs' et
         | true :: bs' => matchCount (fun w => st (.pop0 :: w)) bs' et)

@[simp] theorem matchCount_nil (st : Chromogram → Bool) (bs : List Bool) :
    matchCount st bs [] = if st [] then 1 else 0 := rfl

@[simp] theorem matchCount_c0 (st : Chromogram → Bool) (bs : List Bool) (et : List Color) :
    matchCount st bs (.c0 :: et) = 0 := rfl

@[simp] theorem matchCount_c1 (st : Chromogram → Bool) (bs : List Bool) (et : List Color) :
    matchCount st bs (.c1 :: et) = matchCount (fun w => st (.skip :: w)) bs et := rfl

theorem matchCount_c2_nil (st : Chromogram → Bool) (et : List Color) :
    matchCount st [] (.c2 :: et) = matchCount (fun w => st (.push :: w)) [false] et := rfl

theorem matchCount_c2_false (st : Chromogram → Bool) (bs : List Bool) (et : List Color) :
    matchCount st (false :: bs) (.c2 :: et)
      = matchCount (fun w => st (.push :: w)) (false :: false :: bs) et
        + matchCount (fun w => st (.pop0 :: w)) bs et := rfl

theorem matchCount_c2_true (st : Chromogram → Bool) (bs : List Bool) (et : List Color) :
    matchCount st (true :: bs) (.c2 :: et)
      = matchCount (fun w => st (.push :: w)) (false :: true :: bs) et
        + matchCount (fun w => st (.pop1 :: w)) bs et := rfl

theorem matchCount_c3_nil (st : Chromogram → Bool) (et : List Color) :
    matchCount st [] (.c3 :: et) = matchCount (fun w => st (.push :: w)) [true] et := rfl

theorem matchCount_c3_false (st : Chromogram → Bool) (bs : List Bool) (et : List Color) :
    matchCount st (false :: bs) (.c3 :: et)
      = matchCount (fun w => st (.push :: w)) (true :: false :: bs) et
        + matchCount (fun w => st (.pop1 :: w)) bs et := rfl

theorem matchCount_c3_true (st : Chromogram → Bool) (bs : List Bool) (et : List Color) :
    matchCount st (true :: bs) (.c3 :: et)
      = matchCount (fun w => st (.push :: w)) (true :: true :: bs) et
        + matchCount (fun w => st (.pop0 :: w)) bs et := rfl

theorem matchpg_nil_iff (bs : List Bool) (w : Chromogram) :
    matchpg bs [] w = true ↔ w = [] := by
  cases w <;> simp

theorem matchCount_ne_zero_iff : ∀ (et : List Color) (st : Chromogram → Bool)
    (bs : List Bool), matchCount st bs et ≠ 0 ↔ ∃ w, st w = true ∧ matchpg bs et w = true := by
  intro et
  induction et with
  | nil =>
    intro st bs
    simp only [matchCount]
    constructor
    · intro h
      refine ⟨[], ?_, rfl⟩
      by_contra hst
      simp only [Bool.not_eq_true] at hst
      rw [hst] at h; simp at h
    · rintro ⟨w, hst, hm⟩
      rw [(matchpg_nil_iff bs w).mp hm] at hst
      rw [hst]; simp
  | cons e et ih =>
    intro st bs
    cases e with
    | c0 =>
      simp only [matchCount, ne_eq, not_true_eq_false, false_iff, not_exists]
      rintro w ⟨_, hm⟩
      cases w with
      | nil => simp at hm
      | cons s w => simp [matchStep] at hm
    | c1 =>
      rw [matchCount, ih]
      constructor
      · rintro ⟨w, hst, hm⟩
        exact ⟨.skip :: w, hst, by simpa [matchStep] using hm⟩
      · rintro ⟨w, hst, hm⟩
        cases w with
        | nil => simp at hm
        | cons s w =>
          cases s <;> simp only [matchpg_cons, matchStep, Option.elim] at hm <;>
            first | exact ⟨w, hst, hm⟩ | simp at hm
    | c2 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c2_nil, ih]
        constructor
        · rintro ⟨w, hst, hm⟩
          exact ⟨.push :: w, hst, by simpa [matchStep] using hm⟩
        · rintro ⟨w, hst, hm⟩
          cases w with
          | nil => simp at hm
          | cons s w =>
            cases s <;> simp only [matchpg_cons, matchStep, Option.elim] at hm <;>
              first | exact ⟨w, hst, hm⟩ | simp at hm
      · cases b
        · rw [matchCount_c2_false]
          constructor
          · intro h
            rcases Nat.eq_zero_or_pos (matchCount (fun w => st (.push :: w))
                (false :: false :: bs) et) with h0 | h0
            · have h1 : matchCount (fun w => st (.pop0 :: w)) bs et ≠ 0 := by omega
              obtain ⟨w, hst, hm⟩ := (ih _ bs).mp h1
              exact ⟨.pop0 :: w, hst, by simpa [matchStep] using hm⟩
            · obtain ⟨w, hst, hm⟩ :=
                (ih (fun w => st (.push :: w)) (false :: false :: bs)).mp (by omega)
              exact ⟨.push :: w, hst, by simpa [matchStep] using hm⟩
          · rintro ⟨w, hst, hm⟩
            cases w with
            | nil => simp at hm
            | cons s w =>
              cases s <;> simp only [matchpg_cons, matchStep, Option.elim] at hm
              · have := (ih (fun w => st (.push :: w)) (false :: false :: bs)).mpr
                  ⟨w, hst, hm⟩
                omega
              · simp at hm
              · have := (ih (fun w => st (.pop0 :: w)) bs).mpr ⟨w, hst, hm⟩
                omega
              · simp at hm
        · rw [matchCount_c2_true]
          constructor
          · intro h
            rcases Nat.eq_zero_or_pos (matchCount (fun w => st (.push :: w))
                (false :: true :: bs) et) with h0 | h0
            · have h1 : matchCount (fun w => st (.pop1 :: w)) bs et ≠ 0 := by omega
              obtain ⟨w, hst, hm⟩ := (ih _ bs).mp h1
              exact ⟨.pop1 :: w, hst, by simpa [matchStep] using hm⟩
            · obtain ⟨w, hst, hm⟩ :=
                (ih (fun w => st (.push :: w)) (false :: true :: bs)).mp (by omega)
              exact ⟨.push :: w, hst, by simpa [matchStep] using hm⟩
          · rintro ⟨w, hst, hm⟩
            cases w with
            | nil => simp at hm
            | cons s w =>
              cases s <;> simp only [matchpg_cons, matchStep, Option.elim] at hm
              · have := (ih (fun w => st (.push :: w)) (false :: true :: bs)).mpr
                  ⟨w, hst, hm⟩
                omega
              · simp at hm
              · simp at hm
              · have := (ih (fun w => st (.pop1 :: w)) bs).mpr ⟨w, hst, hm⟩
                omega
    | c3 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c3_nil, ih]
        constructor
        · rintro ⟨w, hst, hm⟩
          exact ⟨.push :: w, hst, by simpa [matchStep] using hm⟩
        · rintro ⟨w, hst, hm⟩
          cases w with
          | nil => simp at hm
          | cons s w =>
            cases s <;> simp only [matchpg_cons, matchStep, Option.elim] at hm <;>
              first | exact ⟨w, hst, hm⟩ | simp at hm
      · cases b
        · rw [matchCount_c3_false]
          constructor
          · intro h
            rcases Nat.eq_zero_or_pos (matchCount (fun w => st (.push :: w))
                (true :: false :: bs) et) with h0 | h0
            · have h1 : matchCount (fun w => st (.pop1 :: w)) bs et ≠ 0 := by omega
              obtain ⟨w, hst, hm⟩ := (ih _ bs).mp h1
              exact ⟨.pop1 :: w, hst, by simpa [matchStep] using hm⟩
            · obtain ⟨w, hst, hm⟩ :=
                (ih (fun w => st (.push :: w)) (true :: false :: bs)).mp (by omega)
              exact ⟨.push :: w, hst, by simpa [matchStep] using hm⟩
          · rintro ⟨w, hst, hm⟩
            cases w with
            | nil => simp at hm
            | cons s w =>
              cases s <;> simp only [matchpg_cons, matchStep, Option.elim] at hm
              · have := (ih (fun w => st (.push :: w)) (true :: false :: bs)).mpr
                  ⟨w, hst, hm⟩
                omega
              · simp at hm
              · simp at hm
              · have := (ih (fun w => st (.pop1 :: w)) bs).mpr ⟨w, hst, hm⟩
                omega
        · rw [matchCount_c3_true]
          constructor
          · intro h
            rcases Nat.eq_zero_or_pos (matchCount (fun w => st (.push :: w))
                (true :: true :: bs) et) with h0 | h0
            · have h1 : matchCount (fun w => st (.pop0 :: w)) bs et ≠ 0 := by omega
              obtain ⟨w, hst, hm⟩ := (ih _ bs).mp h1
              exact ⟨.pop0 :: w, hst, by simpa [matchStep] using hm⟩
            · obtain ⟨w, hst, hm⟩ :=
                (ih (fun w => st (.push :: w)) (true :: true :: bs)).mp (by omega)
              exact ⟨.push :: w, hst, by simpa [matchStep] using hm⟩
          · rintro ⟨w, hst, hm⟩
            cases w with
            | nil => simp at hm
            | cons s w =>
              cases s <;> simp only [matchpg_cons, matchStep, Option.elim] at hm
              · have := (ih (fun w => st (.push :: w)) (true :: true :: bs)).mpr
                  ⟨w, hst, hm⟩
                omega
              · simp at hm
              · have := (ih (fun w => st (.pop0 :: w)) bs).mpr ⟨w, hst, hm⟩
                omega
              · simp at hm

/-! ### Counting in a gram tree -/

/-- The number of chromograms in `t` matching `et` in the context `bs`. -/
def Gtree.sub (t : Gtree) : List Bool → List Color → ℕ := matchCount (Gtree.mem t)

theorem matchCount_eq_zero : ∀ (et : List Color) (st : Chromogram → Bool) (bs : List Bool),
    (∀ w, st w = false) → matchCount st bs et = 0 := by
  intro et
  induction et with
  | nil => intro st bs h; simp [h]
  | cons e et ih =>
    intro st bs h
    cases e with
    | c0 => rfl
    | c1 => exact ih _ _ fun w => h _
    | c2 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c2_nil]; exact ih _ _ fun w => h _
      · cases b
        · rw [matchCount_c2_false, ih _ _ fun w => h _, ih _ _ fun w => h _]
        · rw [matchCount_c2_true, ih _ _ fun w => h _, ih _ _ fun w => h _]
    | c3 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c3_nil]; exact ih _ _ fun w => h _
      · cases b
        · rw [matchCount_c3_false, ih _ _ fun w => h _, ih _ _ fun w => h _]
        · rw [matchCount_c3_true, ih _ _ fun w => h _, ih _ _ fun w => h _]

theorem matchCount_congr : ∀ (et : List Color) (st st' : Chromogram → Bool)
    (bs : List Bool), (∀ w, st w = st' w) → matchCount st bs et = matchCount st' bs et := by
  intro et
  induction et with
  | nil => intro st st' bs h; simp [h]
  | cons e et ih =>
    intro st st' bs h
    cases e with
    | c0 => rfl
    | c1 => exact ih _ _ _ fun w => h _
    | c2 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c2_nil, matchCount_c2_nil]; exact ih _ _ _ fun w => h _
      · cases b
        · rw [matchCount_c2_false, matchCount_c2_false, ih _ (fun w => st' (.push :: w)) _
            fun w => h _, ih _ (fun w => st' (.pop0 :: w)) _ fun w => h _]
        · rw [matchCount_c2_true, matchCount_c2_true, ih _ (fun w => st' (.push :: w)) _
            fun w => h _, ih _ (fun w => st' (.pop1 :: w)) _ fun w => h _]
    | c3 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c3_nil, matchCount_c3_nil]; exact ih _ _ _ fun w => h _
      · cases b
        · rw [matchCount_c3_false, matchCount_c3_false, ih _ (fun w => st' (.push :: w)) _
            fun w => h _, ih _ (fun w => st' (.pop1 :: w)) _ fun w => h _]
        · rw [matchCount_c3_true, matchCount_c3_true, ih _ (fun w => st' (.push :: w)) _
            fun w => h _, ih _ (fun w => st' (.pop0 :: w)) _ fun w => h _]

@[simp] theorem Gtree.sub_empty (bs : List Bool) (et : List Color) :
    Gtree.sub .empty bs et = 0 :=
  matchCount_eq_zero et _ bs fun w => Gtree.mem_empty w

theorem Gtree.sub_node_of_length_le_one {t₀ t₁ t₂ t₃ : Gtree} {et : List Color}
    (h : et.length ≤ 1) (bs : List Bool) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) bs et = 0 := by
  match et with
  | [] => simp [Gtree.sub]
  | [e] =>
    cases e with
    | c0 => rfl
    | c1 => simp [Gtree.sub]
    | c2 =>
      rcases bs with _ | ⟨b, bs⟩
      · simp [Gtree.sub, matchCount_c2_nil]
      · cases b <;> simp [Gtree.sub, matchCount_c2_false, matchCount_c2_true]
    | c3 =>
      rcases bs with _ | ⟨b, bs⟩
      · simp [Gtree.sub, matchCount_c3_nil]
      · cases b <;> simp [Gtree.sub, matchCount_c3_false, matchCount_c3_true]
  | _ :: _ :: _ => simp at h

/-! ### Partitions -/

/-- `st'` and `st''` partition `st`: they are exclusive, and their union is `st`. -/
def SgtreePartition (st st' st'' : Chromogram → Bool) : Prop :=
  ∀ w, if st w then st' w ≠ st'' w else st' w = false ∧ st'' w = false

theorem matchCount_partition : ∀ (et : List Color) (st st' st'' : Chromogram → Bool)
    (bs : List Bool), SgtreePartition st st' st'' →
    matchCount st bs et = matchCount st' bs et + matchCount st'' bs et := by
  intro et
  induction et with
  | nil =>
    intro st st' st'' bs h
    have := h []
    simp only [matchCount_nil]
    split at this
    · rename_i hst
      rw [hst]
      revert this
      cases hs' : st' [] <;> cases hs'' : st'' [] <;> simp
    · rename_i hst
      obtain ⟨h1, h2⟩ := this
      simp [hst, h1, h2]
  | cons e et ih =>
    intro st st' st'' bs h
    have hsub : ∀ s : GramSymbol, SgtreePartition (fun w => st (s :: w))
        (fun w => st' (s :: w)) (fun w => st'' (s :: w)) := fun s w => h (s :: w)
    cases e with
    | c0 => rfl
    | c1 => exact ih _ _ _ _ (hsub .skip)
    | c2 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c2_nil, matchCount_c2_nil, matchCount_c2_nil]
        exact ih _ _ _ _ (hsub .push)
      · cases b
        · rw [matchCount_c2_false, matchCount_c2_false, matchCount_c2_false,
            ih _ _ _ _ (hsub .push), ih _ _ _ _ (hsub .pop0)]
          omega
        · rw [matchCount_c2_true, matchCount_c2_true, matchCount_c2_true,
            ih _ _ _ _ (hsub .push), ih _ _ _ _ (hsub .pop1)]
          omega
    | c3 =>
      rcases bs with _ | ⟨b, bs⟩
      · rw [matchCount_c3_nil, matchCount_c3_nil, matchCount_c3_nil]
        exact ih _ _ _ _ (hsub .push)
      · cases b
        · rw [matchCount_c3_false, matchCount_c3_false, matchCount_c3_false,
            ih _ _ _ _ (hsub .push), ih _ _ _ _ (hsub .pop1)]
          omega
        · rw [matchCount_c3_true, matchCount_c3_true, matchCount_c3_true,
            ih _ _ _ _ (hsub .push), ih _ _ _ _ (hsub .pop0)]
          omega

/-! ### The restriction pair -/

/-- A node with four empty subtrees. -/
def Gtree.empty4 : Gtree → Bool
  | .node t₀ t₁ t₂ t₃ => t₀.isEmpty && t₁.isEmpty && t₂.isEmpty && t₃.isEmpty
  | _ => false

theorem Gtree.empty4_node_iff {t₀ t₁ t₂ t₃ : Gtree} :
    Gtree.empty4 (.node t₀ t₁ t₂ t₃) = true ↔
      t₀ = .empty ∧ t₁ = .empty ∧ t₂ = .empty ∧ t₃ = .empty := by
  simp only [Gtree.empty4, Bool.and_eq_true, Gtree.isEmpty_eq_true, and_assoc]

theorem Gtree.mem_eq_false_of_empty4 {t : Gtree} (h : Gtree.empty4 t = true)
    (w : Chromogram) : Gtree.mem t w = false := by
  match t with
  | .node t₀ t₁ t₂ t₃ =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Gtree.empty4_node_iff.mp h
    cases w with
    | nil => rfl
    | cons s w => cases s <;> simp
  | .leaf0 | .leaf1 | .leaf2 | .leaf3 | .leaf01 | .leaf12 | .leaf13 | .leaf23
  | .empty => simp [Gtree.empty4] at h

/-- A pair of trees partitions a tree. -/
def PairPartition (t : Gtree) (p : Gtree × Gtree) : Prop :=
  SgtreePartition (Gtree.mem t) (Gtree.mem p.1) (Gtree.mem p.2)

/-- Assemble four restriction pairs into one, reusing `t` when a whole side is
empty. -/
def consPairs (t : Gtree) (p₀ p₁ p₂ p₃ : Gtree × Gtree) : Gtree × Gtree :=
  if Gtree.empty4 (.node p₀.1 p₁.1 p₂.1 p₃.1) then (p₀.1, t)
  else if Gtree.empty4 (.node p₀.2 p₁.2 p₂.2 p₃.2) then (t, p₀.2)
  else (.node p₀.1 p₁.1 p₂.1 p₃.1, .node p₀.2 p₁.2 p₂.2 p₃.2)

private theorem partition_of_left_empty {t l : Gtree} (h : ∀ w, Gtree.mem l w = false) :
    SgtreePartition (Gtree.mem t) (Gtree.mem l) (Gtree.mem t) := by
  intro w
  rw [h w]
  split
  · rename_i ht; rw [ht]; simp
  · rename_i ht; simp only [Bool.not_eq_true] at ht; exact ⟨rfl, ht⟩

private theorem partition_of_right_empty {t r : Gtree} (h : ∀ w, Gtree.mem r w = false) :
    SgtreePartition (Gtree.mem t) (Gtree.mem t) (Gtree.mem r) := by
  intro w
  rw [h w]
  split
  · rename_i ht; rw [ht]; simp
  · rename_i ht; simp only [Bool.not_eq_true] at ht; exact ⟨ht, rfl⟩

theorem consPairs_partition {t₀ t₁ t₂ t₃ : Gtree} {p₀ p₁ p₂ p₃ : Gtree × Gtree}
    (h₀ : PairPartition t₀ p₀) (h₁ : PairPartition t₁ p₁)
    (h₂ : PairPartition t₂ p₂) (h₃ : PairPartition t₃ p₃) :
    PairPartition (.node t₀ t₁ t₂ t₃) (consPairs (.node t₀ t₁ t₂ t₃) p₀ p₁ p₂ p₃) := by
  rw [PairPartition, consPairs]
  split
  · rename_i he
    obtain ⟨hp, -, -, -⟩ := Gtree.empty4_node_iff.mp he
    simpa [hp] using partition_of_left_empty (t := Gtree.node t₀ t₁ t₂ t₃)
      (l := Gtree.empty) (fun w => Gtree.mem_empty w)
  · split
    · rename_i he
      obtain ⟨hp, -, -, -⟩ := Gtree.empty4_node_iff.mp he
      simpa [hp] using partition_of_right_empty (t := Gtree.node t₀ t₁ t₂ t₃)
        (r := Gtree.empty) (fun w => Gtree.mem_empty w)
    · intro w
      cases w with
      | nil => simp
      | cons s w => cases s <;> simp only [Gtree.mem_node_cons, Gtree.sel] <;>
          first
            | exact h₀ w | exact h₁ w | exact h₂ w | exact h₃ w

end FourColor

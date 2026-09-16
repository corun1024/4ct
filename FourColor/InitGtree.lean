import FourColor.Gtree
import FourColor.Dyck
import FourColor.InitCtree

/-!
# The initial chromogram tree

The tree of all balanced partial chromograms for a given ring size, built by
dynamic programming as for the initial colouring tree.

The central count is `matchCount_gspec`: the number of balanced chromograms
matching a trace, in a context of `d` open chords, is `genDyck (d+1)` of the
number of high-bit colours in the completed trace.  The two-branch Dyck
recurrence `genDyck (m+1) (n+1) = genDyck (m+2) n + genDyck m n` is exactly the
split of `matchCount` at a `c2` or `c3` into its *push* and *pop* contributions,
which is why these particular numbers appear.

## References

Gonthier's `theories/proof/initgtree.v`.
-/

namespace FourColor

open Color

/-- The specification of the initial gram tree in a context of `d` open chords
and parity `b0`: partial chromograms of length `h` whose completion is balanced. -/
def gspec (h d : ℕ) (b0 : Bool) (w : Chromogram) : Bool :=
  (w.length == h) && balanced d b0 (cgram d b0 w)

/-- The specification of the initial gram tree. -/
def initGtreeSpec (h : ℕ) (w : Chromogram) : Bool := gspec h 0 false w

@[simp] theorem gspec_nil (h d : ℕ) (b0 : Bool) :
    gspec h d b0 [] = ((0 == h) && balanced d b0 (cgram d b0 [])) := rfl

theorem gspec_cons_push (h d : ℕ) (b0 : Bool) (w : Chromogram) :
    gspec (h + 1) d b0 (.push :: w) = gspec h (d + 1) b0 w := by
  simp [gspec, cgram_cons, cgramDepth, cgramBit]

theorem gspec_cons_skip (h d : ℕ) (b0 : Bool) (w : Chromogram) :
    gspec (h + 1) d b0 (.skip :: w) = gspec h d (!b0) w := by
  simp [gspec, cgram_cons, cgramDepth, cgramBit]

theorem gspec_cons_pop0 (h d : ℕ) (b0 : Bool) (w : Chromogram) :
    gspec (h + 1) (d + 1) b0 (.pop0 :: w) = gspec h d b0 w := by
  simp [gspec, cgram_cons, cgramDepth, cgramBit]

theorem gspec_cons_pop1 (h d : ℕ) (b0 : Bool) (w : Chromogram) :
    gspec (h + 1) (d + 1) b0 (.pop1 :: w) = gspec h d (!b0) w := by
  simp [gspec, cgram_cons, cgramDepth, cgramBit]

/-- The completed trace in a context of open chords. -/
abbrev closeG (lb : List Bool) (b0 : Bool) (et : List Color) : List Color :=
  et ++ [closingColor lb b0 + et.sum]

theorem closeG_cons (lb lb' : List Bool) (b0 b0' : Bool) (e : Color) (et : List Color)
    (h : closingColor lb' b0' = closingColor lb b0 + e) :
    closeG lb b0 (e :: et) = e :: closeG lb' b0' et := by
  simp only [closeG, List.cons_append, List.sum_cons, h]
  congr 2
  rw [← add_assoc]

/-! ### Small Dyck values -/

theorem genDyck_zero_eq (m : ℕ) : genDyck m 0 = if m = 1 then 1 else 0 := by
  match m with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem genDyck_one_eq (m : ℕ) : genDyck m 1 = if m = 2 then 1 else 0 := by
  match m with
  | 0 => rfl
  | k + 1 =>
    rw [genDyck_succ_succ, genDyck_zero_eq, genDyck_zero_eq]
    rcases Nat.eq_or_lt_of_le (Nat.zero_le k) with hk | hk
    · simp [← hk]
    · match k, hk with
      | 1, _ => rfl
      | (j + 2), _ => simp [show ¬(j + 2 + 2 = 1) from by omega, show ¬(j + 2 = 1) from by omega,
          show ¬(j + 2 + 1 = 2) from by omega]

/-! ### Counting balanced chromograms -/

theorem closingColor_cons_false (lb : List Bool) (b0 : Bool) :
    closingColor (false :: lb) b0 = closingColor lb b0 + Color.c2 := by
  simp only [closingColor, List.parityLen_cons, List.xorAll_cons, Bool.false_xor]
  cases hp : lb.parityLen <;> cases b0 <;> cases hx : lb.xorAll <;> decide

theorem closingColor_cons_true (lb : List Bool) (b0 : Bool) :
    closingColor (true :: lb) b0 = closingColor lb b0 + Color.c3 := by
  simp only [closingColor, List.parityLen_cons, List.xorAll_cons]
  cases hp : lb.parityLen <;> cases b0 <;> cases hx : lb.xorAll <;> decide

theorem closingColor_not (lb : List Bool) (b0 : Bool) :
    closingColor lb (!b0) = closingColor lb b0 + Color.c1 := by
  simp only [closingColor]
  cases hp : lb.parityLen <;> cases b0 <;> cases hx : lb.xorAll <;> decide

theorem gspec_comp_push (h d : ℕ) (b0 : Bool) :
    (fun w => gspec (h + 1) d b0 (GramSymbol.push :: w)) = gspec h (d + 1) b0 := by
  funext w; exact gspec_cons_push h d b0 w

theorem gspec_comp_skip (h d : ℕ) (b0 : Bool) :
    (fun w => gspec (h + 1) d b0 (GramSymbol.skip :: w)) = gspec h d (!b0) := by
  funext w; exact gspec_cons_skip h d b0 w

theorem gspec_comp_pop0 (h d : ℕ) (b0 : Bool) :
    (fun w => gspec (h + 1) (d + 1) b0 (GramSymbol.pop0 :: w)) = gspec h d b0 := by
  funext w; exact gspec_cons_pop0 h d b0 w

theorem gspec_comp_pop1 (h d : ℕ) (b0 : Bool) :
    (fun w => gspec (h + 1) (d + 1) b0 (GramSymbol.pop1 :: w)) = gspec h d (!b0) := by
  funext w; exact gspec_cons_pop1 h d b0 w

@[simp] theorem genDyck_zero_left (n : ℕ) : genDyck 0 n = 0 := by cases n <;> rfl

private theorem ite_add_ite {p : Prop} [Decidable p] (a b : ℕ) :
    (if p then a else 0) + (if p then b else 0) = if p then a + b else 0 := by
  by_cases h : p <;> simp [h]

private theorem cond_congr_cons {k : ℕ} {e : Color} {et : List Color} {L : List Color}
    (he : e ≠ 0) :
    ((e :: et).length = k + 1 ∧ (0 : Color) ∉ e :: L) ↔ (et.length = k ∧ (0 : Color) ∉ L) := by
  simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, not_or]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ⟨fun hc => he hc.symm, h.2⟩⟩⟩

/-- The push/pop split at a `c2` or `c3` is exactly the two-branch Dyck
recurrence. -/
private theorem two_branch (k n : ℕ) (et L : List Color) (e : Color)
    (he : e ≠ 0) (hc : countHi (e :: L) = countHi L + 1) :
    ((if et.length = k ∧ (0 : Color) ∉ L then genDyck (n + 2) (countHi L) else 0)
      + if et.length = k ∧ (0 : Color) ∉ L then genDyck n (countHi L) else 0)
      = if (e :: et).length = k + 1 ∧ (0 : Color) ∉ e :: L
        then genDyck (n + 1) (countHi (e :: L)) else 0 := by
  rw [ite_add_ite, if_congr (cond_congr_cons he) rfl rfl, hc]
  split
  · exact (genDyck_succ_succ n (countHi L)).symm
  · rfl

/-- In the empty context there is no pop branch, and `genDyck 0` vanishes. -/
private theorem one_branch (k : ℕ) (et L : List Color) (e : Color)
    (he : e ≠ 0) (hc : countHi (e :: L) = countHi L + 1) :
    (if et.length = k ∧ (0 : Color) ∉ L then genDyck 2 (countHi L) else 0)
      = if (e :: et).length = k + 1 ∧ (0 : Color) ∉ e :: L
        then genDyck 1 (countHi (e :: L)) else 0 := by
  rw [if_congr (cond_congr_cons he) rfl rfl, hc]
  split
  · have hr := genDyck_succ_succ 0 (countHi L)
    simp only [genDyck_zero_left, Nat.add_zero] at hr
    exact hr.symm
  · rfl

/-- The number of balanced chromograms matching a trace, in a context of `d`
open chords, is `genDyck (d+1)` of the high-bit count of the completed trace. -/
theorem matchCount_gspec : ∀ (et : List Color) (h d : ℕ) (lb : List Bool) (b0 : Bool),
    d = lb.length →
    matchCount (gspec h d b0) lb et =
      if et.length = h ∧ (0 : Color) ∉ closeG lb b0 et
      then genDyck (d + 1) (countHi (closeG lb b0 et)) else 0 := by
  intro et
  induction et with
  | nil =>
    intro h d lb b0 hd
    subst hd
    match h with
    | k + 1 =>
      rw [if_neg (by rintro ⟨hl, -⟩; simp at hl)]
      simp [gspec]
    | 0 =>
      have hclose : closeG lb b0 [] = [closingColor lb b0] := by simp [closeG]
      rw [hclose, matchCount_nil]
      match lb with
      | [] =>
        cases b0 <;>
          simp [gspec, cgram, balanced, closingColor, Color.ofBits, countHi]
      | [x] =>
        have hc : (closingColor [x] b0).hi = true := by
          cases x <;> cases b0 <;> simp [closingColor, Color.ofBits]
        have hne : (0 : Color) ∉ [closingColor [x] b0] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          intro hz; rw [← hz] at hc; simp at hc
        rw [ite_eq_left (⟨rfl, hne⟩ : ([] : List Color).length = 0 ∧
            (0 : Color) ∉ [closingColor [x] b0]),
          show countHi [closingColor [x] b0] = 1 from by simp [countHi, hc],
          show ([x] : List Bool).length + 1 = 2 from rfl, genDyck_one_eq]
        cases b0 <;> simp [gspec, cgram, balanced]
      | x :: y :: lb' =>
        have hzero : gspec 0 (x :: y :: lb').length b0 [] = false := by
          cases b0 <;> simp [gspec, cgram, balanced]
        have hval : genDyck ((x :: y :: lb').length + 1)
            (countHi [closingColor (x :: y :: lb') b0]) = 0 := by
          have hm : (x :: y :: lb').length + 1 = lb'.length + 3 := by
            simp only [List.length_cons]
          have hcnt : countHi [closingColor (x :: y :: lb') b0] = 0 ∨
              countHi [closingColor (x :: y :: lb') b0] = 1 := by
            simp only [countHi, List.countP_cons, List.countP_nil, Nat.zero_add]
            split <;> simp
          rw [hm]
          rcases hcnt with hc | hc <;> rw [hc]
          · rw [genDyck_zero_eq]; exact if_neg (by omega)
          · rw [genDyck_one_eq]; exact if_neg (by omega)
        rw [hzero]
        simp only [Bool.false_eq_true, ite_false, hval, ite_self]
  | cons e et ih =>
    intro h d lb b0 hd
    match h with
    | 0 =>
      rw [if_neg (by rintro ⟨hl, -⟩; simp at hl)]
      by_contra hne
      obtain ⟨w, hst, hm⟩ := (matchCount_ne_zero_iff (e :: et) _ lb).mp hne
      have hwl := matchpg_length (e :: et) lb w hm
      simp only [gspec, Bool.and_eq_true, beq_iff_eq] at hst
      simp only [List.length_cons] at hwl
      omega
    | k + 1 =>
      subst hd
      cases e with
      | c0 =>
        rw [if_neg (by rintro ⟨-, hm⟩; exact hm (by simp [closeG]))]
        rfl
      | c1 =>
        rw [matchCount_c1, gspec_comp_skip, ih k lb.length lb (!b0) rfl,
          closeG_cons lb lb b0 (!b0) Color.c1 et (closingColor_not lb b0),
          if_congr (cond_congr_cons (e := Color.c1) (by decide)).symm rfl rfl]
        simp
      | c2 =>
        rcases lb with _ | ⟨x, lb⟩
        · simp only [List.length_nil]
          rw [matchCount_c2_nil, gspec_comp_push k 0 b0, ih k 1 [false] b0 rfl,
            closeG_cons [] [false] b0 b0 Color.c2 et (closingColor_cons_false [] b0)]
          exact one_branch k et (closeG [false] b0 et) Color.c2 (by decide) (by simp)
        · cases x
          · have hcl2 : closingColor lb b0 = closingColor (false :: lb) b0 + Color.c2 := by
              rw [closingColor_cons_false, add_assoc,
                show Color.c2 + Color.c2 = 0 from rfl, add_zero]
            have hcleq : closeG (false :: false :: lb) b0 et = closeG lb b0 et := by
              simp only [closeG]
              rw [closingColor_cons_false, ← hcl2]
            simp only [List.length_cons]
            rw [matchCount_c2_false, gspec_comp_push k (lb.length + 1) b0,
              gspec_comp_pop0 k lb.length b0,
              ih k (lb.length + 2) (false :: false :: lb) b0 (by simp),
              ih k lb.length lb b0 rfl, hcleq,
              closeG_cons (false :: lb) lb b0 b0 Color.c2 et hcl2]
            exact two_branch k (lb.length + 1) et (closeG lb b0 et) Color.c2
              (by decide) (by simp)
          · have hcl2 : closingColor lb (!b0) = closingColor (true :: lb) b0 + Color.c2 := by
              rw [closingColor_cons_true, closingColor_not, add_assoc,
                show Color.c3 + Color.c2 = Color.c1 from rfl]
            have hcleq : closeG (false :: true :: lb) b0 et = closeG lb (!b0) et := by
              simp only [closeG]
              rw [closingColor_cons_false, ← hcl2]
            simp only [List.length_cons]
            rw [matchCount_c2_true, gspec_comp_push k (lb.length + 1) b0,
              gspec_comp_pop1 k lb.length b0,
              ih k (lb.length + 2) (false :: true :: lb) b0 (by simp),
              ih k lb.length lb (!b0) rfl, hcleq,
              closeG_cons (true :: lb) lb b0 (!b0) Color.c2 et hcl2]
            exact two_branch k (lb.length + 1) et (closeG lb (!b0) et) Color.c2
              (by decide) (by simp)
      | c3 =>
        rcases lb with _ | ⟨x, lb⟩
        · simp only [List.length_nil]
          rw [matchCount_c3_nil, gspec_comp_push k 0 b0, ih k 1 [true] b0 rfl,
            closeG_cons [] [true] b0 b0 Color.c3 et (closingColor_cons_true [] b0)]
          exact one_branch k et (closeG [true] b0 et) Color.c3 (by decide) (by simp)
        · cases x
          · have hcl2 : closingColor lb (!b0) = closingColor (false :: lb) b0 + Color.c3 := by
              rw [closingColor_cons_false, closingColor_not, add_assoc,
                show Color.c2 + Color.c3 = Color.c1 from rfl]
            have hcleq : closeG (true :: false :: lb) b0 et = closeG lb (!b0) et := by
              simp only [closeG]
              rw [closingColor_cons_true, ← hcl2]
            simp only [List.length_cons]
            rw [matchCount_c3_false, gspec_comp_push k (lb.length + 1) b0,
              gspec_comp_pop1 k lb.length b0,
              ih k (lb.length + 2) (true :: false :: lb) b0 (by simp),
              ih k lb.length lb (!b0) rfl, hcleq,
              closeG_cons (false :: lb) lb b0 (!b0) Color.c3 et hcl2]
            exact two_branch k (lb.length + 1) et (closeG lb (!b0) et) Color.c3
              (by decide) (by simp)
          · have hcl2 : closingColor lb b0 = closingColor (true :: lb) b0 + Color.c3 := by
              rw [closingColor_cons_true, add_assoc,
                show Color.c3 + Color.c3 = 0 from rfl, add_zero]
            have hcleq : closeG (true :: true :: lb) b0 et = closeG lb b0 et := by
              simp only [closeG]
              rw [closingColor_cons_true, ← hcl2]
            simp only [List.length_cons]
            rw [matchCount_c3_true, gspec_comp_push k (lb.length + 1) b0,
              gspec_comp_pop0 k lb.length b0,
              ih k (lb.length + 2) (true :: true :: lb) b0 (by simp),
              ih k lb.length lb b0 rfl, hcleq,
              closeG_cons (true :: lb) lb b0 b0 Color.c3 et hcl2]
            exact two_branch k (lb.length + 1) et (closeG lb b0 et) Color.c3
              (by decide) (by simp)

theorem balanced_cgram_nil (d : ℕ) (b : Bool) :
    balanced d b (cgram d b []) = if d = 0 then b else (d == 1) := by
  match d with
  | 0 => cases b <;> simp [cgram, balanced]
  | 1 => cases b <;> simp [cgram, balanced]
  | _ + 2 => cases b <;> simp [cgram, balanced]

/-! ### The tabulated construction

The initial gram tree is built by the same dynamic programme as the initial
colouring tree.  Unlike `CtreeTable`, only the *length* of a `GtreeTable`
depends on the ring size.
-/

/-- A table of gram-tree pairs, indexed by the number of open chords. -/
abbrev GtreeTable := List (Gtree × Gtree)

/-- The table of all trees of height one. -/
def initGtreeH1 : GtreeTable :=
  [(.leaf01, .leaf0), (.leaf13, .leaf12), (.leaf23, .leaf23)]

/-- Merge three adjacent table entries into the entry one level up. -/
def gtreeMergePairs (p₀ p₁ p₂ : Gtree × Gtree) : Gtree × Gtree :=
  (.node p₀.1 p₁.2 p₂.1 p₂.2, .node p₀.2 p₁.1 p₂.2 p₂.1)

/-- Compute one line of the table. -/
def gtreeMergeLine :
    (Gtree × Gtree) → (Gtree × Gtree) → (Gtree × Gtree) → GtreeTable → ℕ → GtreeTable
  | p₀, p₁, p₂, _, 0 => [gtreeMergePairs p₀ p₁ p₂]
  | p₀, p₁, p₂, [], _ + 1 =>
      [gtreeMergePairs p₀ p₁ p₂,
       gtreeMergePairs (.empty, .empty) p₀ p₁,
       gtreeMergePairs (.empty, .empty) (.empty, .empty) p₀]
  | p₀, p₁, p₂, p :: lpt, d + 1 =>
      gtreeMergePairs p₀ p₁ p₂ :: gtreeMergeLine p p₀ p₁ lpt d

/-- The table of subtrees of height `h + 1` in a context of `d` open chords. -/
def gtreeInitTable : ℕ → ℕ → GtreeTable
  | _, 0 => initGtreeH1
  | d, h + 1 =>
      match gtreeInitTable (d + 1) h with
      | p₁ :: p₀ :: lpt => gtreeMergeLine p₀ p₁ (.empty, .empty) lpt d
      | tab => tab

/-- The tree of all balanced partial chromograms for ring size `h`. -/
def gtreeInitTree (h : ℕ) : Gtree :=
  match h, gtreeInitTable 0 (h - 1) with
  | _ + 1, (t, _) :: _ => t
  | _, _ => .empty

/-- The entry of a table at a given open-chord count and parity. -/
def gtreeTableSub (tab : GtreeTable) (n : ℕ) (b : Bool) : Gtree :=
  let p := tab.getD n (.empty, .empty)
  if b then p.2 else p.1

@[simp] theorem gtreeTableSub_nil (n : ℕ) (b : Bool) :
    gtreeTableSub [] n b = .empty := by cases b <;> rfl

/-- The height-one table is correct: its entries are exactly the one-symbol
chromograms balanced in the corresponding context. -/
theorem mem_initGtreeH1 (dw : ℕ) (bw : Bool) (w : Chromogram) :
    Gtree.mem (gtreeTableSub initGtreeH1 dw bw) w = gspec 1 dw bw w := by
  match w with
  | [] => cases dw <;> cases bw <;> simp [gspec, gtreeTableSub, initGtreeH1, Gtree.mem]
  | [s] =>
    match dw with
    | 0 => cases bw <;> cases s <;> decide
    | 1 => cases bw <;> cases s <;> decide
    | 2 => cases bw <;> cases s <;> decide
    | n + 3 =>
      have hempty : gtreeTableSub initGtreeH1 (n + 3) bw = .empty := by
        cases bw <;> simp [gtreeTableSub, initGtreeH1]
      rw [hempty, Gtree.mem_empty]
      cases s <;> cases bw <;>
        simp [gspec, cgram_cons, cgramDepth, cgramBit, balanced, balanced_cgram_nil]
  | s :: s' :: w' =>
    have hlen : gspec 1 dw bw (s :: s' :: w') = false := by
      simp [gspec]
    rw [hlen]
    match dw with
    | 0 => cases bw <;> cases s <;> simp [gtreeTableSub, initGtreeH1, Gtree.mem, Gtree.leafMem]
    | 1 => cases bw <;> cases s <;> simp [gtreeTableSub, initGtreeH1, Gtree.mem, Gtree.leafMem]
    | 2 => cases bw <;> cases s <;> simp [gtreeTableSub, initGtreeH1, Gtree.mem, Gtree.leafMem]
    | _ + 3 => cases bw <;> simp [gtreeTableSub, initGtreeH1]

/-! ### Correctness of the tabulation

Each line of the table is computed from the (longer) line one level down, and
its `dw`-th entry describes the chromograms of a context of `dw` open chords
only as long as `dw ≤ d`, where `d` is the context the line was built for.  That
bound, together with the length bound that keeps the next line well defined, is
the invariant of the induction on the height (`gtreeInitTable_spec`).
-/

theorem gspec_cons_pop0_zero (h : ℕ) (b0 : Bool) (w : Chromogram) :
    gspec h 0 b0 (.pop0 :: w) = false := by
  simp [gspec, cgram_cons]

theorem gspec_cons_pop1_zero (h : ℕ) (b0 : Bool) (w : Chromogram) :
    gspec h 0 b0 (.pop1 :: w) = false := by
  simp [gspec, cgram_cons]

@[simp] theorem gtreeTableSub_cons_zero (p : Gtree × Gtree) (tab : GtreeTable) (b : Bool) :
    gtreeTableSub (p :: tab) 0 b = if b then p.2 else p.1 := rfl

@[simp] theorem gtreeTableSub_cons_succ (p : Gtree × Gtree) (tab : GtreeTable) (n : ℕ)
    (b : Bool) : gtreeTableSub (p :: tab) (n + 1) b = gtreeTableSub tab n b := rfl

theorem gtreeTableSub_of_length_le : ∀ (tab : GtreeTable) (n : ℕ) (b : Bool),
    tab.length ≤ n → gtreeTableSub tab n b = .empty := by
  intro tab
  induction tab with
  | nil => intro n b _; exact gtreeTableSub_nil n b
  | cons p tab ih =>
    intro n b hn
    match n with
    | 0 => simp at hn
    | n + 1 =>
      rw [gtreeTableSub_cons_succ]
      exact ih n b (by simpa using hn)

theorem mem_gtreeTableSub_eq_false (tab : GtreeTable) (n : ℕ) (b : Bool)
    (hn : tab.length ≤ n) (w : Chromogram) : Gtree.mem (gtreeTableSub tab n b) w = false := by
  rw [gtreeTableSub_of_length_le tab n b hn]
  exact Gtree.mem_empty w

@[simp] theorem gtreeMergeLine_zero (p₀ p₁ p₂ : Gtree × Gtree) (lpt : GtreeTable) :
    gtreeMergeLine p₀ p₁ p₂ lpt 0 = [gtreeMergePairs p₀ p₁ p₂] := by
  cases lpt <;> rfl

@[simp] theorem gtreeMergeLine_nil_succ (p₀ p₁ p₂ : Gtree × Gtree) (d : ℕ) :
    gtreeMergeLine p₀ p₁ p₂ [] (d + 1) =
      [gtreeMergePairs p₀ p₁ p₂, gtreeMergePairs (.empty, .empty) p₀ p₁,
        gtreeMergePairs (.empty, .empty) (.empty, .empty) p₀] := rfl

@[simp] theorem gtreeMergeLine_cons_succ (p₀ p₁ p₂ p : Gtree × Gtree) (lpt : GtreeTable)
    (d : ℕ) : gtreeMergeLine p₀ p₁ p₂ (p :: lpt) (d + 1) =
      gtreeMergePairs p₀ p₁ p₂ :: gtreeMergeLine p p₀ p₁ lpt d := rfl

/-- Every line starts with the merge of its three seed entries. -/
private theorem gtreeTableSub_mergeLine_zero (p₀ p₁ p₂ : Gtree × Gtree) (lpt : GtreeTable)
    (d : ℕ) (b : Bool) :
    gtreeTableSub (gtreeMergeLine p₀ p₁ p₂ lpt d) 0 b =
      if b then (gtreeMergePairs p₀ p₁ p₂).2 else (gtreeMergePairs p₀ p₁ p₂).1 := by
  match d, lpt with
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, _ :: _ => rfl

/-- Every line is nonempty. -/
theorem one_le_gtreeMergeLine_length (p₀ p₁ p₂ : Gtree × Gtree) (lpt : GtreeTable) (d : ℕ) :
    1 ≤ (gtreeMergeLine p₀ p₁ p₂ lpt d).length := by
  match d, lpt with
  | 0, lpt => simp [gtreeMergeLine_zero]
  | _ + 1, [] => simp
  | _ + 1, p :: lpt =>
    simp only [gtreeMergeLine_cons_succ, List.length_cons]
    omega

/-- The `dw`-th entry of a merged line is, as far as membership is concerned,
the node assembled from the entries of index `dw`, `dw + 1` and `dw + 2` of the
line it was computed from, prefixed by the seed pair `p₂`.  Beyond the end of
the shorter line both sides are empty, which is why this only holds for
membership and not as an equality of trees. -/
private theorem mem_gtreeTableSub_mergeLine : ∀ (dw d : ℕ), dw ≤ d →
    ∀ (p₀ p₁ p₂ : Gtree × Gtree) (lpt : GtreeTable) (bw : Bool) (w : Chromogram),
      Gtree.mem (gtreeTableSub (gtreeMergeLine p₀ p₁ p₂ lpt d) dw bw) w =
        Gtree.mem (.node (gtreeTableSub (p₂ :: p₁ :: p₀ :: lpt) (dw + 1 + 1) bw)
          (gtreeTableSub (p₂ :: p₁ :: p₀ :: lpt) (dw + 1) (!bw))
          (gtreeTableSub (p₂ :: p₁ :: p₀ :: lpt) dw bw)
          (gtreeTableSub (p₂ :: p₁ :: p₀ :: lpt) dw (!bw))) w := by
  intro dw
  induction dw with
  | zero =>
    intro d _ p₀ p₁ p₂ lpt bw w
    rw [gtreeTableSub_mergeLine_zero]
    cases bw <;> rfl
  | succ dw ih =>
    intro d hd p₀ p₁ p₂ lpt bw w
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hd' : dw ≤ d := by omega
    match lpt with
    | p :: lpt =>
      rw [gtreeMergeLine_cons_succ, gtreeTableSub_cons_succ, ih d hd' p p₀ p₁ lpt bw w]
      simp only [gtreeTableSub_cons_succ]
    | [] =>
      rcases dw with _ | _ | k
      · cases bw <;> rfl
      · cases bw <;> rfl
      · refine Eq.trans (mem_gtreeTableSub_eq_false _ _ _ ?_ w) ?_
        · simp only [gtreeMergeLine_nil_succ, List.length_cons, List.length_nil]
          omega
        · cases w with
          | nil => simp
          | cons s w =>
            cases s <;>
              simp only [Gtree.mem_node_cons, Gtree.sel_node_push, Gtree.sel_node_skip,
                Gtree.sel_node_pop0, Gtree.sel_node_pop1] <;>
              exact (mem_gtreeTableSub_eq_false _ _ _
                (by simp only [List.length_cons, List.length_nil]; omega) w).symm

/-- The tabulation is correct: the entries of index at most `d` of the table of
height `h + 1` for a context of `d` open chords are the trees of the partial
chromograms of length `h + 1` whose completion is balanced.  The length bound in
the first component is what makes the next line well defined. -/
private theorem gtreeInitTable_spec : ∀ (h d : ℕ),
    (1 ≤ (gtreeInitTable d h).length ∧ (d ≠ 0 → 2 ≤ (gtreeInitTable d h).length)) ∧
      ∀ (dw : ℕ) (bw : Bool) (w : Chromogram), dw ≤ d →
        Gtree.mem (gtreeTableSub (gtreeInitTable d h) dw bw) w = gspec (h + 1) dw bw w := by
  intro h
  induction h with
  | zero =>
    intro d
    have h0 : gtreeInitTable d 0 = initGtreeH1 := rfl
    refine ⟨⟨?_, fun _ => ?_⟩, fun dw bw w _ => ?_⟩
    · rw [h0]; simp [initGtreeH1]
    · rw [h0]; simp [initGtreeH1]
    · rw [h0]; exact mem_initGtreeH1 dw bw w
  | succ h ih =>
    intro d
    obtain ⟨⟨-, hlen2⟩, Dsub⟩ := ih (d + 1)
    have hlen : 2 ≤ (gtreeInitTable (d + 1) h).length := hlen2 (Nat.succ_ne_zero d)
    match htab : gtreeInitTable (d + 1) h with
    | [] => rw [htab] at hlen; simp at hlen
    | [_] => rw [htab] at hlen; simp at hlen
    | p₁ :: p₀ :: lpt =>
      rw [htab] at Dsub
      have hline : gtreeInitTable d (h + 1)
          = gtreeMergeLine p₀ p₁ (.empty, .empty) lpt d := by
        simp only [gtreeInitTable, htab]
      refine ⟨⟨?_, fun hd => ?_⟩, fun dw bw w hdw => ?_⟩
      · rw [hline]
        exact one_le_gtreeMergeLine_length _ _ _ lpt d
      · obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        rw [hline]
        match lpt with
        | [] => simp
        | p :: lpt =>
          have h1 := one_le_gtreeMergeLine_length p p₀ p₁ lpt d
          simp only [gtreeMergeLine_cons_succ, List.length_cons]
          omega
      · rw [hline, mem_gtreeTableSub_mergeLine dw d hdw p₀ p₁ (.empty, .empty) lpt bw w]
        cases w with
        | nil => simp [gspec]
        | cons s w =>
          cases s with
          | push =>
            rw [Gtree.mem_node_cons, Gtree.sel_node_push, gtreeTableSub_cons_succ,
              Dsub (dw + 1) bw w (by omega), gspec_cons_push]
          | skip =>
            rw [Gtree.mem_node_cons, Gtree.sel_node_skip, gtreeTableSub_cons_succ,
              Dsub dw (!bw) w (by omega), gspec_cons_skip]
          | pop0 =>
            rcases dw with _ | dw
            · rw [Gtree.mem_node_cons, Gtree.sel_node_pop0, gtreeTableSub_cons_zero,
                gspec_cons_pop0_zero]
              cases bw <;> simp
            · rw [Gtree.mem_node_cons, Gtree.sel_node_pop0, gtreeTableSub_cons_succ,
                Dsub dw bw w (by omega), gspec_cons_pop0]
          | pop1 =>
            rcases dw with _ | dw
            · rw [Gtree.mem_node_cons, Gtree.sel_node_pop1, gtreeTableSub_cons_zero,
                gspec_cons_pop1_zero]
              cases bw <;> simp
            · rw [Gtree.mem_node_cons, Gtree.sel_node_pop1, gtreeTableSub_cons_succ,
                Dsub dw (!bw) w (by omega), gspec_cons_pop1]

/-- The specialisation of `matchCount_gspec` to the empty context: the number of
balanced chromograms matching a trace is the Dyck number of the high-bit count
of its completion.  This is the reference's `match_count_balanced`. -/
theorem matchCount_initGtreeSpec (h : ℕ) (et : List Color) :
    matchCount (initGtreeSpec h) [] et =
      if et.length = h ∧ (0 : Color) ∉ completeTrace et
      then dyck (countHi (completeTrace et)) else 0 := by
  have hcl : closeG [] false et = completeTrace et := by
    simp [closeG, completeTrace, closingColor, Color.ofBits]
  rw [matchCount_congr et (initGtreeSpec h) (gspec h 0 false) [] fun _ => rfl,
    matchCount_gspec et h 0 [] false rfl, hcl]
  rfl

/-- The initial gram tree contains exactly the balanced partial chromograms of
the ring size: the reference's `gtree_mem_init_tree`. -/
theorem mem_gtreeInitTree (h : ℕ) (w : Chromogram) :
    Gtree.mem (gtreeInitTree h) w = initGtreeSpec h w := by
  match h with
  | 0 =>
    have h0 : gtreeInitTree 0 = .empty := rfl
    rw [h0, Gtree.mem_empty]
    match w with
    | [] => rfl
    | _ :: _ => simp [initGtreeSpec, gspec]
  | h + 1 =>
    obtain ⟨⟨hlen, -⟩, Dsub⟩ := gtreeInitTable_spec h 0
    match htab : gtreeInitTable 0 h with
    | [] => rw [htab] at hlen; simp at hlen
    | p :: tab =>
      rw [htab] at Dsub
      have htree : gtreeInitTree (h + 1) = gtreeTableSub (p :: tab) 0 false := by
        obtain ⟨t, t'⟩ := p
        simp only [gtreeInitTree, Nat.add_sub_cancel, htab, gtreeTableSub_cons_zero,
          Bool.false_eq_true, ite_false]
      rw [htree, Dsub 0 false w (Nat.le_refl 0), initGtreeSpec]

end FourColor

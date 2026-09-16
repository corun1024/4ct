import Mathlib.Tactic.IntervalCases
import FourColor.Geometry

/-!
# Parts: patterns for the second neighbourhood of a dart

A *part* describes the second neighbourhood of a dart `x` of a plain cubic
hypermap by giving a range of arities for each face that occurs in it.  The
faces are grouped into *subparts*, listed counterclockwise around the *hub*
(the face of `x`).  A subpart consists of a *spoke* (a face adjacent to the
hub), a *hat* (the face between this spoke and the previous one) and possibly
some *fans* (the faces adjacent to the spoke only, counted counterclockwise
from the hat).

As in the reference the list structure is merged into the record structure:
there are four kinds of subpart, according to the number of known fans, and a
subpart with `n` known fans fixes the arity of its spoke to `n + 5`.  The
fitting predicate and all the part comparison functions really do branch on
these four shapes, so this representation is kept.

## Main definitions

* `PRange` — arity ranges, `prMN` meaning `[M, N]` with `N = 9` unbounded;
  `PRange.Mem`, `PRange.cmp`, `PRange.meet`, `PRange.splitRange`.
* `PartRel` — the outcome of comparing two sets: `disjoint`, `straddle`,
  `subset`; `PartRel.Holds`, `PartRel.notSubset`, `PartRel.meet`.
* `SubpartLoc` — a position inside a subpart, and `SubpartLoc.dart`, the dart
  of the face it points at.
* `Part` — parts and part sectors, with the list operations `Part.size`,
  `Part.cat`, `Part.take`, `Part.drop`, `Part.rot`, `Part.rev`,
  `Part.mirror`, and the accessors `Part.spoke`, `Part.hat`, `Part.fan1R`, ….
* `Part.cmp`, `Part.meet` — comparison and intersection of parts.
* `Part.GoodSplit`, `Part.splitPart` — splitting the range at one location of
  one subpart at an arity bound.
* `Hypermap.Fitp`, `Hypermap.ExactFitp`, `Hypermap.TightFitp` — the fitting
  predicates, and `Hypermap.PartUpdate`, the validity of a part constructor
  with a hole at a given location.

## Main results

* `PRange.mem_cmp`, `PRange.mem_meet`, `PRange.mem_splitRange` — correctness of
  the range operations.
* `Hypermap.fitp_cat`, `Hypermap.fitp_drop`, `Hypermap.exact_fitp_rot` — how
  fitting interacts with the list operations.
* `Hypermap.fitp_cmp`, `Hypermap.fitp_meet` — correctness of `Part.cmp` and
  `Part.meet`.
* `Hypermap.fitp_split` — a dart fits a split part exactly when it fits the
  part and its arity at the split location is on the right side of the cut.
* `Hypermap.fitp_mirror`, `Hypermap.fitp_sym` — a dart fits the mirror image of
  a part exactly when it fits the part in the mirror hypermap.
* `Hypermap.fitp_converse` — the converse of a part fits the dart two face
  steps back from its third spoke.

## Implementation notes

Ranges are encoded by their bounds rather than by the reference's two
fifteen-by-fifteen tables: `PRange.cmp` and `PRange.meet` are defined by
comparing `PRange.lo` and `PRange.hi`, and `PRange.ofBounds` inverts them,
which is possible because the fifteen constructors realise exactly the fifteen
pairs `5 ≤ lo ≤ hi ≤ 9`.  The two definitions agree with the reference tables,
and the correctness lemmas become arithmetic rather than a `15 × 15 × 10` case
analysis.  Likewise `PRange.GoodRSplit` is defined by the inequalities
`lo ≤ k < hi` that the reference's `cmp_range r (prange_lo k) = Pstraddle`
expresses; `PRange.goodRSplit_iff` proves the two agree.

Boolean-valued predicates of the reference are `Prop`-valued here, with
`Decidable` instances where the argument is decidable; `Hypermap.Fitp` is not
decidable as stated because `Hypermap.arity` is noncomputable.

The fitting theorems that depend on the geometry of the hypermap
(`Hypermap.fitp_mirror`, `Hypermap.fitp_sym` and `Hypermap.fitp_converse`) are
proved at the end of the file, after the arity computations they need.  They
are stated through `Hypermap.ars`, the arity of the face across the `n`-th
edge counterclockwise from a spoke, which is the shape all the subpart
locations but the spoke have.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file
corresponds to `theories/proof/part.v` of the Coq development.
-/

namespace FourColor

/-! ### Ranges of arities -/

/-- The arity ranges a part can impose on a face other than the hub: `prMN` is
the range `[M, N]`, where `N = 9` means unbounded.  So `pr59` is the free range
in a pentagonal map and `pr99` means "at least 9". -/
inductive PRange
  | pr55 | pr66 | pr77 | pr88 | pr99
  | pr56 | pr67 | pr78 | pr89
  | pr57 | pr68 | pr79
  | pr58 | pr69
  | pr59
  deriving DecidableEq, Repr

namespace PRange

/-- The lower bound of a range. -/
def lo : PRange → ℕ
  | pr55 | pr56 | pr57 | pr58 | pr59 => 5
  | pr66 | pr67 | pr68 | pr69 => 6
  | pr77 | pr78 | pr79 => 7
  | pr88 | pr89 => 8
  | pr99 => 9

/-- The upper bound of a range; the value `9` means that the range is
unbounded. -/
def hi : PRange → ℕ
  | pr55 => 5
  | pr66 | pr56 => 6
  | pr77 | pr67 | pr57 => 7
  | pr88 | pr78 | pr68 | pr58 => 8
  | pr99 | pr89 | pr79 | pr69 | pr59 => 9

/-- Membership in a range: at least the lower bound, and at most the upper
bound unless the range is unbounded. -/
def Mem (r : PRange) (n : ℕ) : Prop := r.lo ≤ n ∧ (n ≤ r.hi ∨ r.hi = 9)

instance (r : PRange) (n : ℕ) : Decidable (r.Mem n) := by unfold Mem; infer_instance

/-- Every range starts at `5` or later. -/
theorem five_le_lo (r : PRange) : 5 ≤ r.lo := by cases r <;> decide

/-- Ranges are nonempty. -/
theorem lo_le_hi (r : PRange) : r.lo ≤ r.hi := by cases r <;> decide

/-- Upper bounds are at most `9`, the unbounded marker. -/
theorem hi_le_nine (r : PRange) : r.hi ≤ 9 := by cases r <;> decide

/-- Membership in the free range is just the pentagonal bound. -/
@[simp] theorem mem_pr59 (n : ℕ) : pr59.Mem n ↔ 5 ≤ n := by
  simp [Mem, lo, hi]

/-- The range `pr55` is the singleton `{5}`. -/
theorem mem_pr55 (n : ℕ) : pr55.Mem n ↔ n = 5 := by
  simp only [Mem, lo, hi]; omega

/-- The range `pr66` is the singleton `{6}`. -/
theorem mem_pr66 (n : ℕ) : pr66.Mem n ↔ n = 6 := by
  simp only [Mem, lo, hi]; omega

/-- The range `pr77` is the singleton `{7}`. -/
theorem mem_pr77 (n : ℕ) : pr77.Mem n ↔ n = 7 := by
  simp only [Mem, lo, hi]; omega

/-- The range `pr88` is the singleton `{8}`. -/
theorem mem_pr88 (n : ℕ) : pr88.Mem n ↔ n = 8 := by
  simp only [Mem, lo, hi]; omega

/-- The range with the given bounds, for `5 ≤ lo ≤ hi ≤ 9`; the fifteen
constructors realise exactly these fifteen pairs. -/
def ofBounds : ℕ → ℕ → PRange
  | 5, 5 => pr55
  | 5, 6 => pr56
  | 5, 7 => pr57
  | 5, 8 => pr58
  | 6, 6 => pr66
  | 6, 7 => pr67
  | 6, 8 => pr68
  | 6, 9 => pr69
  | 7, 7 => pr77
  | 7, 8 => pr78
  | 7, 9 => pr79
  | 8, 8 => pr88
  | 8, 9 => pr89
  | 9, 9 => pr99
  | _, _ => pr59

/-- The fifteen ranges are exactly the fifteen pairs of bounds. -/
@[simp] theorem ofBounds_lo_hi (r : PRange) : ofBounds r.lo r.hi = r := by
  cases r <;> rfl

/-- The lower bound of a range built from bounds in range. -/
theorem lo_ofBounds {a b : ℕ} (ha : 5 ≤ a) (hab : a ≤ b) (hb : b ≤ 9) :
    (ofBounds a b).lo = a := by
  have ha' : a ≤ 9 := le_trans hab hb
  interval_cases a <;> interval_cases b <;> rfl

/-- The upper bound of a range built from bounds in range. -/
theorem hi_ofBounds {a b : ℕ} (ha : 5 ≤ a) (hab : a ≤ b) (hb : b ≤ 9) :
    (ofBounds a b).hi = b := by
  have ha' : a ≤ 9 := le_trans hab hb
  interval_cases a <;> interval_cases b <;> rfl

end PRange

/-! ### Comparison outcomes -/

/-- The outcome of comparing a set with another one: they are disjoint, the
first is contained in the second, or neither (`straddle`, which also covers
strict containment the other way round). -/
inductive PartRel
  | disjoint | straddle | subset
  deriving DecidableEq, Repr

namespace PartRel

/-- The expected outcome of a membership test in the second set, for an element
of the first set, given how the two sets compare. -/
def Holds : PartRel → Prop → Prop
  | disjoint, _ => False
  | straddle, P => P
  | subset, _ => True

/-- Weaken `subset` to `straddle`, leaving the other outcomes alone.  This is
used when the second set carries a constraint that the first one ignores. -/
def notSubset : PartRel → PartRel
  | subset => straddle
  | c => c

/-- The comparison outcome for the products `A × A'` and `B × B'` of sets whose
components compare as `c` and `c'`. -/
def meet : PartRel → PartRel → PartRel
  | disjoint, _ => disjoint
  | subset, c' => c'
  | straddle, c' => c'.notSubset

/-- A weakened comparison is never `subset`. -/
@[simp] theorem notSubset_ne_subset (c : PartRel) : c.notSubset ≠ subset := by
  cases c <;> simp [notSubset]

/-- Weakening does not create or destroy disjointness. -/
@[simp] theorem notSubset_eq_disjoint (c : PartRel) :
    c.notSubset = disjoint ↔ c = disjoint := by
  cases c <;> simp [notSubset]

/-- A product is contained in another exactly when both factors are. -/
@[simp] theorem meet_eq_subset (c c' : PartRel) :
    c.meet c' = subset ↔ c = subset ∧ c' = subset := by
  cases c <;> cases c' <;> simp [meet, notSubset]

/-- A product is disjoint from another exactly when some factor is. -/
@[simp] theorem meet_eq_disjoint (c c' : PartRel) :
    c.meet c' = disjoint ↔ c = disjoint ∨ c' = disjoint := by
  cases c <;> cases c' <;> simp [meet, notSubset]

/-- A comparison outcome is determined by the two tests it predicts. -/
theorem holds_iff {c : PartRel} {P : Prop} (hs : c = subset → P)
    (hd : c = disjoint → ¬ P) : P ↔ c.Holds P := by
  cases c
  · simp [Holds, hd rfl]
  · simp [Holds]
  · simp [Holds, hs rfl]

end PartRel

/-! ### Range comparison, meet and splitting -/

namespace PRange

/-- Set comparison of two ranges. -/
def cmp (r r' : PRange) : PartRel :=
  if r.hi < r'.lo ∨ r'.hi < r.lo then .disjoint
  else if r'.lo ≤ r.lo ∧ r.hi ≤ r'.hi then .subset
  else .straddle

/-- Intersection of two ranges; the result is meaningful when the ranges are
not disjoint. -/
def meet (r r' : PRange) : PRange := ofBounds (max r.lo r'.lo) (min r.hi r'.hi)

/-- An arity in a range contained in another one is in that one. -/
theorem mem_of_cmp_eq_subset {r r' : PRange} {n : ℕ} (h : r.cmp r' = .subset)
    (hn : r.Mem n) : r'.Mem n := by
  have h1 := hi_le_nine r
  have h2 := hi_le_nine r'
  simp only [Mem] at hn ⊢
  simp only [cmp] at h
  split_ifs at h with hd hs
  omega

/-- An arity in a range is outside every range disjoint from it. -/
theorem not_mem_of_cmp_eq_disjoint {r r' : PRange} {n : ℕ} (h : r.cmp r' = .disjoint)
    (hn : r.Mem n) : ¬ r'.Mem n := by
  have h1 := hi_le_nine r
  have h2 := hi_le_nine r'
  have h3 := lo_le_hi r
  have h4 := lo_le_hi r'
  simp only [Mem] at hn ⊢
  simp only [cmp] at h
  split_ifs at h with hd hs
  omega

/-- The comparison of two ranges predicts the membership test in the second
one, for an arity in the first. -/
theorem mem_cmp {r : PRange} {n : ℕ} (hn : r.Mem n) (r' : PRange) :
    r'.Mem n ↔ (r.cmp r').Holds (r'.Mem n) :=
  PartRel.holds_iff (fun h => mem_of_cmp_eq_subset h hn)
    (fun h => not_mem_of_cmp_eq_disjoint h hn)

/-- The meet of two overlapping ranges is their intersection. -/
theorem mem_meet_iff {r r' : PRange} (h : max r.lo r'.lo ≤ min r.hi r'.hi) (n : ℕ) :
    (r.meet r').Mem n ↔ r.Mem n ∧ r'.Mem n := by
  have h1 := hi_le_nine r
  have h2 := hi_le_nine r'
  have h5 := five_le_lo r
  have h6 := five_le_lo r'
  simp only [Mem, meet]
  rw [lo_ofBounds (by omega) (by omega) (by omega),
    hi_ofBounds (by omega) (by omega) (by omega)]
  omega

/-- An arity in both ranges is in their meet. -/
theorem mem_meet {r r' : PRange} {n : ℕ} (h : r.Mem n) (h' : r'.Mem n) :
    (r.meet r').Mem n := by
  have h1 := hi_le_nine r
  have h2 := hi_le_nine r'
  have h3 := lo_le_hi r
  have h4 := lo_le_hi r'
  have h5 := five_le_lo r
  have h6 := five_le_lo r'
  simp only [Mem] at h h'
  rw [mem_meet_iff (by omega)]
  exact ⟨h, h'⟩

/-- The range `[5, k]`, or the free range when `k` is out of bounds. -/
def rangeLo (k : ℕ) : PRange :=
  match k with
  | 5 => pr55
  | 6 => pr56
  | 7 => pr57
  | 8 => pr58
  | _ => pr59

/-- The range `[k + 1, 9]`, or the free range when `k` is out of bounds. -/
def rangeHi (k : ℕ) : PRange :=
  match k with
  | 5 => pr69
  | 6 => pr79
  | 7 => pr89
  | 8 => pr99
  | _ => pr59

/-- The lower half of a split always starts at `5`. -/
theorem lo_rangeLo : ∀ k : ℕ, (rangeLo k).lo = 5
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

/-- The lower half of a split at an arity in range stops at that arity. -/
theorem hi_rangeLo {k : ℕ} (h5 : 5 ≤ k) (h8 : k ≤ 8) : (rangeLo k).hi = k := by
  interval_cases k <;> rfl

/-- Below `5` the lower half of a split is the whole free range. -/
theorem hi_rangeLo_of_lt {k : ℕ} (h : k < 5) : (rangeLo k).hi = 9 := by
  interval_cases k <;> rfl

/-- Above `8` the lower half of a split is the whole free range. -/
theorem hi_rangeLo_of_gt {k : ℕ} (h : 8 < k) : (rangeLo k).hi = 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 9 := ⟨k - 9, by omega⟩
  rfl

/-- The upper half of a split at an arity in range starts just above it. -/
theorem lo_rangeHi {k : ℕ} (h5 : 5 ≤ k) (h8 : k ≤ 8) : (rangeHi k).lo = k + 1 := by
  interval_cases k <;> rfl

/-- The upper half of a split is always unbounded. -/
theorem hi_rangeHi : ∀ k : ℕ, (rangeHi k).hi = 9
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

/-- A range can be split at `k` when it straddles `[5, k]`. -/
def GoodRSplit (k : ℕ) (r : PRange) : Prop := r.lo ≤ k ∧ k < r.hi

instance (k : ℕ) (r : PRange) : Decidable (GoodRSplit k r) := by
  unfold GoodRSplit; infer_instance

/-- A split is possible exactly where the comparison with `[5, k]` straddles;
this is the reference's definition of a good split. -/
theorem goodRSplit_iff (k : ℕ) (r : PRange) :
    GoodRSplit k r ↔ r.cmp (rangeLo k) = .straddle := by
  have h1 := hi_le_nine r
  have h2 := five_le_lo r
  have h3 := lo_le_hi r
  have hA := lo_rangeLo k
  simp only [GoodRSplit, cmp]
  rcases lt_or_ge k 5 with hk | hk
  · rw [hi_rangeLo_of_lt hk]
    split_ifs with hd hs <;> simp <;> omega
  · rcases le_or_gt k 8 with hk8 | hk8
    · rw [hi_rangeLo hk hk8]
      split_ifs with hd hs <;> simp <;> omega
    · rw [hi_rangeLo_of_gt hk8]
      split_ifs with hd hs <;> simp <;> omega

/-- The lower (`lo = true`) or upper half of a range, cut at `k`. -/
def splitRange (k : ℕ) (lo : Bool) (r : PRange) : PRange :=
  meet (cond lo (rangeLo k) (rangeHi k)) r

/-- The arity condition selecting a half of a split. -/
def SplitCond (lo : Bool) (k n : ℕ) : Prop := cond lo (n ≤ k) (k < n)

instance : ∀ (lo : Bool) (k n : ℕ), Decidable (SplitCond lo k n)
  | true, k, n => inferInstanceAs (Decidable (n ≤ k))
  | false, k, n => inferInstanceAs (Decidable (k < n))

/-- Membership in a half of a split range: the half of the condition, and the
range itself. -/
theorem mem_splitRange {k : ℕ} {r : PRange} (hr : GoodRSplit k r) (lo : Bool) (n : ℕ) :
    (splitRange k lo r).Mem n ↔ SplitCond lo k n ∧ r.Mem n := by
  have h1 := hi_le_nine r
  have h2 := five_le_lo r
  have h3 := lo_le_hi r
  obtain ⟨hk1, hk2⟩ := hr
  have hk5 : 5 ≤ k := by omega
  have hk8 : k ≤ 8 := by omega
  cases lo with
  | true =>
    have hA : (rangeLo k).lo = 5 := lo_rangeLo k
    have hB : (rangeLo k).hi = k := hi_rangeLo hk5 hk8
    simp only [splitRange, SplitCond, Bool.cond_true]
    rw [mem_meet_iff (by rw [hA, hB]; omega)]
    simp only [Mem, hA, hB]
    omega
  | false =>
    have hA : (rangeHi k).lo = k + 1 := lo_rangeHi hk5 hk8
    have hB : (rangeHi k).hi = 9 := hi_rangeHi k
    simp only [splitRange, SplitCond, Bool.cond_false]
    rw [mem_meet_iff (by rw [hA, hB]; omega)]
    simp only [Mem, hA, hB, or_true, and_true]
    omega

end PRange

/-! ### Locations inside a subpart -/

/-- A face position inside a subpart: the spoke, the hat, or one of the three
possible fans. -/
inductive SubpartLoc
  | spoke | hat | fan1 | fan2 | fan3
  deriving DecidableEq, Repr

namespace SubpartLoc

variable {D : Type*}

/-- The dart, in the face at this location of the first subpart at `x`, that
the fitting predicate measures the arity of. -/
def dart : SubpartLoc → Hypermap D → D → D
  | spoke, G, x => G.edge x
  | hat, G, x => G.edge (G.face^[2] (G.edge x))
  | fan1, G, x => G.edge (G.face^[3] (G.edge x))
  | fan2, G, x => G.edge (G.face^[4] (G.edge x))
  | fan3, G, x => G.edge (G.face^[5] (G.edge x))

end SubpartLoc

/-! ### Parts -/

/-- A part, or a sector of one: a list of subparts, each consisting of a spoke,
a hat and possibly some fans.  A subpart with `n` known fans has a spoke of
arity `n + 5`, so only the hat and the fans need a range; `cons` is the case of
a subpart with no known fan, whose spoke range is then arbitrary. -/
inductive Part
  | nil
  | cons (spoke hat : PRange) (p : Part)
  | cons6 (hat fan1 : PRange) (p : Part)
  | cons7 (hat fan1 fan2 : PRange) (p : Part)
  | cons8 (hat fan1 fan2 fan3 : PRange) (p : Part)
  deriving DecidableEq, Repr

namespace Part

/-- A subpart with the given spoke range and a free hat range. -/
def consS (s : PRange) (p : Part) : Part := cons s .pr59 p

/-- The part with `n` completely free subparts; it fits any dart of arity `n`
in a pentagonal map. -/
def free : ℕ → Part
  | 0 => nil
  | n + 1 => cons .pr59 .pr59 (free n)

/-- The number of subparts of a part, that is, the hub arity it describes. -/
def size : Part → ℕ
  | nil => 0
  | cons _ _ p | cons6 _ _ p | cons7 _ _ _ p | cons8 _ _ _ _ p => p.size + 1

/-- The sector left by dropping the first `n` subparts. -/
def drop : ℕ → Part → Part
  | 0, p => p
  | _ + 1, nil => nil
  | n + 1, cons _ _ p => drop n p
  | n + 1, cons6 _ _ p => drop n p
  | n + 1, cons7 _ _ _ p => drop n p
  | n + 1, cons8 _ _ _ _ p => drop n p

/-- The sector consisting of the first `n` subparts. -/
def take : ℕ → Part → Part
  | 0, _ => nil
  | _ + 1, nil => nil
  | n + 1, cons s h p => cons s h (take n p)
  | n + 1, cons6 h f1 p => cons6 h f1 (take n p)
  | n + 1, cons7 h f1 f2 p => cons7 h f1 f2 (take n p)
  | n + 1, cons8 h f1 f2 f3 p => cons8 h f1 f2 f3 (take n p)

/-- Concatenation of two parts. -/
def cat : Part → Part → Part
  | nil, q => q
  | cons s h p, q => cons s h (cat p q)
  | cons6 h f1 p, q => cons6 h f1 (cat p q)
  | cons7 h f1 f2 p, q => cons7 h f1 f2 (cat p q)
  | cons8 h f1 f2 f3 p, q => cons8 h f1 f2 f3 (cat p q)

/-- The part rotated by `n` subparts; meaningful for `n ≤ p.size`. -/
def rot (n : ℕ) (p : Part) : Part := cat (drop n p) (take n p)

/-- Concatenation of the reversal of the first part with the second one. -/
def catrev : Part → Part → Part
  | nil, q => q
  | cons s h p, q => catrev p (cons s h q)
  | cons6 h f1 p, q => catrev p (cons6 h f1 q)
  | cons7 h f1 f2 p, q => catrev p (cons7 h f1 f2 q)
  | cons8 h f1 f2 f3 p, q => catrev p (cons8 h f1 f2 f3 q)

/-- The reversal of a part.  This is *not* a mirror image: the subparts
themselves are unchanged.  It is used to implement zippers. -/
def rev (p : Part) : Part := catrev p nil

/-! #### Accessors

Except for `nextHat`, these assume the part is not `nil`, and return the free
range otherwise.  The fans are needed in both orders, so there is a clockwise
(`L`) and a counterclockwise (`R`) version of each fan accessor. -/

/-- The arity range of the first spoke. -/
def spoke : Part → PRange
  | cons s _ _ => s
  | cons6 _ _ _ => .pr66
  | cons7 _ _ _ _ => .pr77
  | cons8 _ _ _ _ _ => .pr88
  | nil => .pr59

/-- The range of the first hat, defaulting to `h0` for the empty sector. -/
def nextHat (h0 : PRange) : Part → PRange
  | nil => h0
  | cons _ h _ | cons6 h _ _ | cons7 h _ _ _ | cons8 h _ _ _ _ => h

/-- The arity range of the first hat. -/
def hat (p : Part) : PRange := nextHat .pr59 p

/-- The range of the first counterclockwise fan of the first subpart. -/
def fan1R : Part → PRange
  | cons6 _ f1 _ | cons7 _ f1 _ _ | cons8 _ f1 _ _ _ => f1
  | _ => .pr59

/-- The range of the second counterclockwise fan of the first subpart. -/
def fan2R : Part → PRange
  | cons7 _ _ f2 _ | cons8 _ _ f2 _ _ => f2
  | _ => .pr59

/-- The range of the third counterclockwise fan of the first subpart. -/
def fan3R : Part → PRange
  | cons8 _ _ _ f3 _ => f3
  | _ => .pr59

/-- The range of the first clockwise fan of the first subpart. -/
def fan1L : Part → PRange
  | cons6 _ f _ | cons7 _ _ f _ | cons8 _ _ _ f _ => f
  | _ => .pr59

/-- The range of the second clockwise fan of the first subpart. -/
def fan2L : Part → PRange
  | cons7 _ f _ _ | cons8 _ _ f _ _ => f
  | _ => .pr59

/-- The range of the third clockwise fan of the first subpart. -/
def fan3L : Part → PRange
  | cons8 _ f _ _ _ => f
  | _ => .pr59

/-! #### Mirror image

Reflection across the first spoke: the subparts are listed in the reverse
order, each hat moves to the next subpart, and the fans of each subpart are
reversed. -/

/-- The mirror image of `p`, pushed in front of the accumulator `rp`; `h0` is
the hat that wraps around to the last subpart. -/
def mirrorRec (h0 : PRange) : Part → Part → Part
  | rp, nil => rp
  | rp, cons s _ p => mirrorRec h0 (cons s (nextHat h0 p) rp) p
  | rp, cons6 _ f1 p => mirrorRec h0 (cons6 (nextHat h0 p) f1 rp) p
  | rp, cons7 _ f1 f2 p => mirrorRec h0 (cons7 (nextHat h0 p) f2 f1 rp) p
  | rp, cons8 _ f1 f2 f3 p => mirrorRec h0 (cons8 (nextHat h0 p) f3 f2 f1 rp) p

/-- The mirror image of a part: the reflection across its first spoke. -/
def mirror (p : Part) : Part := mirrorRec p.hat nil p

/-! #### Properties of the list operations -/

/-- The free part of size `n` has `n` subparts. -/
@[simp] theorem size_free (n : ℕ) : (free n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [free, size, ih]

/-- The empty sector is a right unit for concatenation. -/
@[simp] theorem cat_nil (p : Part) : cat p nil = p := by
  induction p <;> simp_all [cat]

/-- Concatenation of parts is associative. -/
theorem cat_assoc (p q r : Part) : cat (cat p q) r = cat p (cat q r) := by
  induction p <;> simp_all [cat]

/-- Concatenation adds sizes. -/
@[simp] theorem size_cat (p q : Part) : (cat p q).size = p.size + q.size := by
  induction p <;> simp_all [cat, size] <;> omega

/-- Dropping subparts removes them from the size. -/
@[simp] theorem size_drop (n : ℕ) (p : Part) : (drop n p).size = p.size - n := by
  induction n generalizing p with
  | zero => simp [drop]
  | succ n ih => cases p <;> simp [drop, size, ih]

/-- Taking subparts keeps at most that many of them. -/
@[simp] theorem size_take (n : ℕ) (p : Part) : (take n p).size = min n p.size := by
  induction n generalizing p with
  | zero => simp [take, size]
  | succ n ih => cases p <;> simp [take, size, ih]

/-- Taking and dropping the same number of subparts splits a part. -/
@[simp] theorem cat_take_drop (n : ℕ) (p : Part) : cat (take n p) (drop n p) = p := by
  induction n generalizing p with
  | zero => simp [take, drop, cat]
  | succ n ih => cases p <;> simp [take, drop, cat, ih]

/-- Rotation does not change the size. -/
@[simp] theorem size_rot (n : ℕ) (p : Part) : (rot n p).size = p.size := by
  simp only [rot, size_cat, size_drop, size_take]
  omega

/-- Reverse concatenation is concatenation with the reversal. -/
theorem catrev_eq_cat : ∀ p q : Part, catrev p q = cat (rev p) q := by
  have key : ∀ p q : Part, catrev p q = cat (catrev p nil) q := by
    intro p
    induction p with
    | nil => intro q; rfl
    | cons s h p ih =>
      intro q
      have e1 : catrev (cons s h p) q = catrev p (cons s h q) := by simp only [catrev]
      have e2 : catrev (cons s h p) nil = catrev p (cons s h nil) := by simp only [catrev]
      rw [e1, e2, ih (cons s h q), ih (cons s h nil), cat_assoc]
      simp only [cat]
    | cons6 h f1 p ih =>
      intro q
      have e1 : catrev (cons6 h f1 p) q = catrev p (cons6 h f1 q) := by simp only [catrev]
      have e2 : catrev (cons6 h f1 p) nil = catrev p (cons6 h f1 nil) := by simp only [catrev]
      rw [e1, e2, ih (cons6 h f1 q), ih (cons6 h f1 nil), cat_assoc]
      simp only [cat]
    | cons7 h f1 f2 p ih =>
      intro q
      have e1 : catrev (cons7 h f1 f2 p) q = catrev p (cons7 h f1 f2 q) := by simp only [catrev]
      have e2 : catrev (cons7 h f1 f2 p) nil = catrev p (cons7 h f1 f2 nil) := by
        simp only [catrev]
      rw [e1, e2, ih (cons7 h f1 f2 q), ih (cons7 h f1 f2 nil), cat_assoc]
      simp only [cat]
    | cons8 h f1 f2 f3 p ih =>
      intro q
      have e1 : catrev (cons8 h f1 f2 f3 p) q = catrev p (cons8 h f1 f2 f3 q) := by
        simp only [catrev]
      have e2 : catrev (cons8 h f1 f2 f3 p) nil = catrev p (cons8 h f1 f2 f3 nil) := by
        simp only [catrev]
      rw [e1, e2, ih (cons8 h f1 f2 f3 q), ih (cons8 h f1 f2 f3 nil), cat_assoc]
      simp only [cat]
  exact key

/-- Reverse concatenation adds sizes. -/
theorem size_catrev (p q : Part) : (catrev p q).size = p.size + q.size := by
  induction p generalizing q with
  | nil => simp [catrev, size]
  | cons s h p ih => simp only [catrev, ih, size]; omega
  | cons6 h f1 p ih => simp only [catrev, ih, size]; omega
  | cons7 h f1 f2 p ih => simp only [catrev, ih, size]; omega
  | cons8 h f1 f2 f3 p ih => simp only [catrev, ih, size]; omega

/-- Reversal does not change the size. -/
@[simp] theorem size_rev (p : Part) : (rev p).size = p.size := by
  simp [rev, size_catrev, size]

/-- Reversing a reverse concatenation swaps its two arguments. -/
private theorem catrev_catrev (p q : Part) : catrev (catrev p q) nil = catrev q p := by
  induction p generalizing q with
  | nil => rfl
  | cons s h p ih => simpa only [catrev] using ih (cons s h q)
  | cons6 h f1 p ih => simpa only [catrev] using ih (cons6 h f1 q)
  | cons7 h f1 f2 p ih => simpa only [catrev] using ih (cons7 h f1 f2 q)
  | cons8 h f1 f2 f3 p ih => simpa only [catrev] using ih (cons8 h f1 f2 f3 q)

/-- Reversal is an involution. -/
@[simp] theorem rev_rev (p : Part) : rev (rev p) = p :=
  catrev_catrev p nil

/-- Mirroring accumulates onto the accumulator. -/
theorem size_mirrorRec (h0 : PRange) (p rp : Part) :
    (mirrorRec h0 rp p).size = p.size + rp.size := by
  induction p generalizing rp with
  | nil => simp [mirrorRec, size]
  | cons s h p ih => simp only [mirrorRec, ih, size]; omega
  | cons6 h f1 p ih => simp only [mirrorRec, ih, size]; omega
  | cons7 h f1 f2 p ih => simp only [mirrorRec, ih, size]; omega
  | cons8 h f1 f2 f3 p ih => simp only [mirrorRec, ih, size]; omega

/-- Mirroring does not change the size. -/
@[simp] theorem size_mirror (p : Part) : p.mirror.size = p.size := by
  simp [mirror, size_mirrorRec, size]

/-- The key step for `mirror_mirror`: mirroring undoes `mirrorRec` as long as
the accumulator's first hat is the one that wraps around. -/
theorem mirror_mirrorRec (h0 : PRange) :
    ∀ p q : Part, nextHat h0 q = nextHat h0 p → (mirrorRec h0 q p).mirror = mirrorRec h0 p q := by
  intro p
  induction p with
  | nil =>
    intro q hq
    cases q <;> simp_all [mirrorRec, mirror, hat, nextHat]
  | cons s h p ih =>
    intro q hq
    simp only [mirrorRec]
    rw [ih (cons s (nextHat h0 p) q) rfl]
    simp only [mirrorRec]
    have hq' : nextHat h0 q = h := hq
    rw [hq']
  | cons6 h f1 p ih =>
    intro q hq
    simp only [mirrorRec]
    rw [ih (cons6 (nextHat h0 p) f1 q) rfl]
    simp only [mirrorRec]
    have hq' : nextHat h0 q = h := hq
    rw [hq']
  | cons7 h f1 f2 p ih =>
    intro q hq
    simp only [mirrorRec]
    rw [ih (cons7 (nextHat h0 p) f2 f1 q) rfl]
    simp only [mirrorRec]
    have hq' : nextHat h0 q = h := hq
    rw [hq']
  | cons8 h f1 f2 f3 p ih =>
    intro q hq
    simp only [mirrorRec]
    rw [ih (cons8 (nextHat h0 p) f3 f2 f1 q) rfl]
    simp only [mirrorRec]
    have hq' : nextHat h0 q = h := hq
    rw [hq']

/-- The mirror image is an involution. -/
@[simp] theorem mirror_mirror (p : Part) : p.mirror.mirror = p := by
  have h : nextHat p.hat nil = nextHat p.hat p := by cases p <;> rfl
  simpa [mirror, mirrorRec] using mirror_mirrorRec p.hat p nil h

/-- Mirroring a sector onto an accumulator appends the accumulator to the
mirror image of the sector. -/
theorem mirrorRec_eq_cat (h0 : PRange) :
    ∀ p rp : Part, mirrorRec h0 rp p = cat (mirrorRec h0 nil p) rp := by
  intro p
  induction p with
  | nil => intro rp; rfl
  | cons s h p ih =>
    intro rp
    simp only [mirrorRec]
    rw [ih, ih (cons s (nextHat h0 p) nil), cat_assoc]
    rfl
  | cons6 h f1 p ih =>
    intro rp
    simp only [mirrorRec]
    rw [ih, ih (cons6 (nextHat h0 p) f1 nil), cat_assoc]
    rfl
  | cons7 h f1 f2 p ih =>
    intro rp
    simp only [mirrorRec]
    rw [ih, ih (cons7 (nextHat h0 p) f2 f1 nil), cat_assoc]
    rfl
  | cons8 h f1 f2 f3 p ih =>
    intro rp
    simp only [mirrorRec]
    rw [ih, ih (cons8 (nextHat h0 p) f3 f2 f1 nil), cat_assoc]
    rfl

/-- The first hat of a mirror image is the hat that wraps around, unless the
mirrored sector is empty. -/
theorem nextHat_mirrorRec (h0 h' : PRange) :
    ∀ p rp : Part, nextHat h' (mirrorRec h0 rp p)
      = if p = nil then nextHat h' rp else h0 := by
  intro p
  induction p with
  | nil => intro rp; simp [mirrorRec]
  | cons s h p ih =>
    intro rp
    change nextHat h' (mirrorRec h0 (cons s (nextHat h0 p) rp) p) = _
    rw [ih]; cases p <;> simp [nextHat]
  | cons6 h f1 p ih =>
    intro rp
    change nextHat h' (mirrorRec h0 (cons6 (nextHat h0 p) f1 rp) p) = _
    rw [ih]; cases p <;> simp [nextHat]
  | cons7 h f1 f2 p ih =>
    intro rp
    change nextHat h' (mirrorRec h0 (cons7 (nextHat h0 p) f2 f1 rp) p) = _
    rw [ih]; cases p <;> simp [nextHat]
  | cons8 h f1 f2 f3 p ih =>
    intro rp
    change nextHat h' (mirrorRec h0 (cons8 (nextHat h0 p) f3 f2 f1 rp) p) = _
    rw [ih]; cases p <;> simp [nextHat]

/-- The first hat of a nonempty mirror image. -/
theorem hat_mirror {p : Part} (h : p ≠ nil) : p.mirror.hat = p.hat := by
  simp [hat, mirror, nextHat_mirrorRec, h]

/-- Mirroring preserves nonemptiness. -/
theorem mirror_ne_nil {p : Part} (h : p ≠ nil) : p.mirror ≠ nil := by
  intro hm
  have hs : p.size = 0 := by
    have := congrArg size hm
    rwa [size_mirror] at this
  exact h (by cases p <;> simp_all [size])


/-! #### Comparison and intersection -/

/-- Set comparison of two parts, viewed as sets of pointed maps.  The second
part is truncated to the length of the first one, as in the reference. -/
def cmp : Part → Part → PartRel
  | _, nil => .subset
  | nil, _ => .straddle
  | cons sp hp p, cons sq hq q =>
      (sp.cmp sq).meet ((hp.cmp hq).meet (cmp p q))
  | cons sp hp p, cons6 hq _ q =>
      ((sp.cmp PRange.pr66).notSubset).meet ((hp.cmp hq).meet (cmp p q))
  | cons sp hp p, cons7 hq _ _ q =>
      ((sp.cmp PRange.pr77).notSubset).meet ((hp.cmp hq).meet (cmp p q))
  | cons sp hp p, cons8 hq _ _ _ q =>
      ((sp.cmp PRange.pr88).notSubset).meet ((hp.cmp hq).meet (cmp p q))
  | cons6 hp _ p, cons sq hq q =>
      (PRange.pr66.cmp sq).meet ((hp.cmp hq).meet (cmp p q))
  | cons6 hp f1p p, cons6 hq f1q q =>
      (hp.cmp hq).meet ((f1p.cmp f1q).meet (cmp p q))
  | cons7 hp _ _ p, cons sq hq q =>
      (PRange.pr77.cmp sq).meet ((hp.cmp hq).meet (cmp p q))
  | cons7 hp f1p f2p p, cons7 hq f1q f2q q =>
      (hp.cmp hq).meet ((f1p.cmp f1q).meet ((f2p.cmp f2q).meet (cmp p q)))
  | cons8 hp _ _ _ p, cons sq hq q =>
      (PRange.pr88.cmp sq).meet ((hp.cmp hq).meet (cmp p q))
  | cons8 hp f1p f2p f3p p, cons8 hq f1q f2q f3q q =>
      (hp.cmp hq).meet ((f1p.cmp f1q).meet ((f2p.cmp f2q).meet ((f3p.cmp f3q).meet (cmp p q))))
  | _, _ => .disjoint

/-- Intersection of a part with a part sector; it truncates the second
argument, and is meaningful when the two are not disjoint. -/
def meet : Part → Part → Part
  | cons sp hp p, cons sq hq q =>
      cons (sp.meet sq) (hp.meet hq) (meet p q)
  | cons _ hp p, cons6 hq f1q q =>
      cons6 (hp.meet hq) f1q (meet p q)
  | cons _ hp p, cons7 hq f1q f2q q =>
      cons7 (hp.meet hq) f1q f2q (meet p q)
  | cons _ hp p, cons8 hq f1q f2q f3q q =>
      cons8 (hp.meet hq) f1q f2q f3q (meet p q)
  | cons6 hp f1p p, cons _ hq q =>
      cons6 (hp.meet hq) f1p (meet p q)
  | cons6 hp f1p p, cons6 hq f1q q =>
      cons6 (hp.meet hq) (f1p.meet f1q) (meet p q)
  | cons7 hp f1p f2p p, cons _ hq q =>
      cons7 (hp.meet hq) f1p f2p (meet p q)
  | cons7 hp f1p f2p p, cons7 hq f1q f2q q =>
      cons7 (hp.meet hq) (f1p.meet f1q) (f2p.meet f2q) (meet p q)
  | cons8 hp f1p f2p f3p p, cons _ hq q =>
      cons8 (hp.meet hq) f1p f2p f3p (meet p q)
  | cons8 hp f1p f2p f3p p, cons8 hq f1q f2q f3q q =>
      cons8 (hp.meet hq) (f1p.meet f1q) (f2p.meet f2q) (f3p.meet f3q) (meet p q)
  | p, _ => p

/-- Meeting with the empty sector leaves a part unchanged. -/
@[simp] theorem meet_nil (p : Part) : p.meet nil = p := by cases p <;> rfl

/-- The empty sector meets every part in the empty sector. -/
@[simp] theorem nil_meet (q : Part) : nil.meet q = nil := by cases q <;> rfl

/-- The meet has the size of its first argument, which it does not truncate. -/
@[simp] theorem size_meet (p q : Part) : (p.meet q).size = p.size := by
  induction p generalizing q with
  | nil => simp [size]
  | cons sp hp p ih =>
    cases q <;> simp [meet, size, ih]
  | cons6 hp f1p p ih =>
    cases q <;> simp [meet, size, ih]
  | cons7 hp f1p f2p p ih =>
    cases q <;> simp [meet, size, ih]
  | cons8 hp f1p f2p f3p p ih =>
    cases q <;> simp [meet, size, ih]

/-! #### Comparison and intersection

The intersection is slightly asymmetric: it truncates its second argument. -/

/-- Every part is contained in the empty sector, which constrains nothing. -/
@[simp] theorem cmp_nil (p : Part) : p.cmp nil = .subset := by cases p <;> rfl

/-- The empty sector constrains nothing, so it straddles any `cons`. -/
@[simp] theorem nil_cmp_cons (s h : PRange) (q : Part) : nil.cmp (cons s h q) = .straddle := rfl

/-- The empty sector constrains nothing, so it straddles any `cons6`. -/
@[simp] theorem nil_cmp_cons6 (h f1 : PRange) (q : Part) :
    nil.cmp (cons6 h f1 q) = .straddle := rfl

/-- The empty sector constrains nothing, so it straddles any `cons7`. -/
@[simp] theorem nil_cmp_cons7 (h f1 f2 : PRange) (q : Part) :
    nil.cmp (cons7 h f1 f2 q) = .straddle := rfl

/-- The empty sector constrains nothing, so it straddles any `cons8`. -/
@[simp] theorem nil_cmp_cons8 (h f1 f2 f3 : PRange) (q : Part) :
    nil.cmp (cons8 h f1 f2 f3 q) = .straddle := rfl

/-! #### The converse part

The converse of a part describes the same second neighbourhood read from the
spoke of another subpart.  The five pieces below assemble it; they are pure data
transformations, and the fitting theorem relating them to `Fitp` is not yet
proved.
-/

/-- The first two sectors of the converse part. -/
def convPart12 : Part → PRange × (Part → Part)
  | .cons s2 s1 (.cons h23 f2 _) =>
      match f2, s2 with
      | .pr59, _ => (h23, fun q => consS s1 (consS s2 q))
      | _, .pr55 => (h23, fun q => consS s1 (.cons .pr55 f2 q))
      | _, .pr66 => (h23, fun q => consS s1 (.cons6 .pr59 f2 q))
      | _, .pr77 => (h23, fun q => consS s1 (.cons7 .pr59 .pr59 f2 q))
      | _, _ => (.pr59, fun _ => .nil)
  | .cons6 s1 h12 (.cons h23 f21 _) => (h23, fun q => consS s1 (.cons6 h12 f21 q))
  | .cons7 s1 h12 f21 (.cons h23 f22 _) => (h23, fun q => consS s1 (.cons7 h12 f21 f22 q))
  | _ => (.pr59, fun _ => .nil)

/-- The third sector of the converse part. -/
def convPart3 (h23 : PRange) : Part → Part → Part
  | .nil => .cons .pr55 h23
  | .cons _ _ .nil => .cons .pr66 h23
  | .cons f31 _ (.cons f32 _ .nil) =>
      match f31, f32 with
      | .pr59, .pr59 => .cons .pr77 h23
      | _, _ => .cons7 h23 f31 f32
  | .cons f31 _ (.cons f32 _ (.cons f33 _ .nil)) => .cons8 h23 f31 f32 f33
  | _ => fun _ => .nil

/-- The fourth sector of the converse part. -/
def convPart4 : Part → PRange × (Part → Part)
  | .cons h34 _ (.cons s4 f41 _) =>
      match f41, s4 with
      | .pr59, _ => (.pr59, .cons s4 h34)
      | _, .pr55 => (f41, .cons .pr55 h34)
      | _, .pr66 => (.pr59, .cons6 h34 f41)
      | _, .pr77 => (.pr59, .cons7 h34 f41 .pr59)
      | _, _ => (.pr59, fun _ => .nil)
  | .cons h34 _ (.cons6 f41 h45 _) => (h45, .cons6 h34 f41)
  | .cons h34 _ (.cons7 f41 f42 h45 _) => (h45, .cons7 h34 f41 f42)
  | _ => (.pr59, fun _ => .nil)

/-- The fifth sector of the converse part. -/
def convPart5 (h45 : PRange) : Part → PRange × Part
  | .cons u s5 _ => (u, .cons s5 h45 .nil)
  | .cons7 s5 s6 s7 _ => (.pr77, .cons s5 h45 (consS s6 (consS s7 .nil)))
  | _ => (.pr59, .nil)

/-- The converse of a part, with the arity range of its new first hat. -/
def conversePart (p1 : Part) : PRange × Part :=
  let (h45, q4) := convPart4 p1
  let (u, q5) := convPart5 h45 (p1.drop 2)
  let (h23, q12) := convPart12 (p1.drop 3)
  let q3 := convPart3 h23 (p1.drop 5)
  (u, q12 (q3 (q4 q5)))

/-! #### Splitting a part at an arity bound

A split is specified by a location `i` inside the subpart number `j`, an arity
`k` and a boolean `lo` saying which half of the range at that location is
kept.  It is *good* when it is nontrivial and definite: the range straddles
`[5, k]` and, at a fan location, the spoke below it has a fixed arity that is
large enough. -/

/-- The split at location `i` of the subpart `j` of `p` is possible. -/
def GoodSplit (i : SubpartLoc) (j k : ℕ) (p : Part) : Prop :=
  match i, p.drop j with
  | .spoke, cons s _ _ => PRange.GoodRSplit k s
  | .hat, cons _ h _ => PRange.GoodRSplit k h
  | .hat, cons6 h _ _ => PRange.GoodRSplit k h
  | .hat, cons7 h _ _ _ => PRange.GoodRSplit k h
  | .hat, cons8 h _ _ _ _ => PRange.GoodRSplit k h
  | .fan1, cons6 _ f1 _ => PRange.GoodRSplit k f1
  | .fan1, cons7 _ f1 _ _ => PRange.GoodRSplit k f1
  | .fan1, cons8 _ f1 _ _ _ => PRange.GoodRSplit k f1
  | .fan1, cons .pr66 _ _ => PRange.GoodRSplit k .pr59
  | .fan1, cons .pr77 _ _ => PRange.GoodRSplit k .pr59
  | .fan1, cons .pr88 _ _ => PRange.GoodRSplit k .pr59
  | .fan2, cons7 _ _ f2 _ => PRange.GoodRSplit k f2
  | .fan2, cons8 _ _ f2 _ _ => PRange.GoodRSplit k f2
  | .fan2, cons .pr77 _ _ => PRange.GoodRSplit k .pr59
  | .fan2, cons .pr88 _ _ => PRange.GoodRSplit k .pr59
  | .fan3, cons8 _ _ _ f3 _ => PRange.GoodRSplit k f3
  | .fan3, cons .pr88 _ _ => PRange.GoodRSplit k .pr59
  | _, _ => False

/-- The part `p` with the range at location `i` of its subpart `j` replaced by
one half of its split at `k`. -/
def splitPart (i : SubpartLoc) (j k : ℕ) (lo : Bool) (p : Part) : Part :=
  match i, p.drop j with
  | .spoke, cons s h p' => (p.take j).cat (cons (PRange.splitRange k lo s) h p')
  | .hat, cons s h p' => (p.take j).cat (cons s (PRange.splitRange k lo h) p')
  | .hat, cons6 h f1 p' => (p.take j).cat (cons6 (PRange.splitRange k lo h) f1 p')
  | .hat, cons7 h f1 f2 p' =>
      (p.take j).cat (cons7 (PRange.splitRange k lo h) f1 f2 p')
  | .hat, cons8 h f1 f2 f3 p' =>
      (p.take j).cat (cons8 (PRange.splitRange k lo h) f1 f2 f3 p')
  | .fan1, cons6 h f1 p' => (p.take j).cat (cons6 h (PRange.splitRange k lo f1) p')
  | .fan1, cons7 h f1 f2 p' =>
      (p.take j).cat (cons7 h (PRange.splitRange k lo f1) f2 p')
  | .fan1, cons8 h f1 f2 f3 p' =>
      (p.take j).cat (cons8 h (PRange.splitRange k lo f1) f2 f3 p')
  | .fan1, cons .pr66 h p' =>
      (p.take j).cat (cons6 h (PRange.splitRange k lo .pr59) p')
  | .fan1, cons .pr77 h p' =>
      (p.take j).cat (cons7 h (PRange.splitRange k lo .pr59) .pr59 p')
  | .fan1, cons .pr88 h p' =>
      (p.take j).cat (cons8 h (PRange.splitRange k lo .pr59) .pr59 .pr59 p')
  | .fan2, cons7 h f1 f2 p' =>
      (p.take j).cat (cons7 h f1 (PRange.splitRange k lo f2) p')
  | .fan2, cons8 h f1 f2 f3 p' =>
      (p.take j).cat (cons8 h f1 (PRange.splitRange k lo f2) f3 p')
  | .fan2, cons .pr77 h p' =>
      (p.take j).cat (cons7 h .pr59 (PRange.splitRange k lo .pr59) p')
  | .fan2, cons .pr88 h p' =>
      (p.take j).cat (cons8 h .pr59 (PRange.splitRange k lo .pr59) .pr59 p')
  | .fan3, cons8 h f1 f2 f3 p' =>
      (p.take j).cat (cons8 h f1 f2 (PRange.splitRange k lo f3) p')
  | .fan3, cons .pr88 h p' =>
      (p.take j).cat (cons8 h .pr59 .pr59 (PRange.splitRange k lo .pr59) p')
  | _, _ => p

/-- A part is split in two by taking and dropping `j` subparts. -/
theorem size_take_add_size_drop (j : ℕ) (p : Part) :
    (p.take j).size + (p.drop j).size = p.size := by
  have := congrArg Part.size (Part.cat_take_drop j p)
  rwa [Part.size_cat] at this

/-- Splitting a range does not change the size of the part. -/
@[simp] theorem size_splitPart (i : SubpartLoc) (j k : ℕ) (lo : Bool) (p : Part) :
    (splitPart i j k lo p).size = p.size := by
  have key : ∀ q : Part, q.size = (p.drop j).size → ((p.take j).cat q).size = p.size := by
    intro q hq
    rw [Part.size_cat, hq, size_take_add_size_drop]
  rcases hd : p.drop j with _ | ⟨s, h, p'⟩ | ⟨h, f1, p'⟩ | ⟨h, f1, f2, p'⟩ |
    ⟨h, f1, f2, f3, p'⟩ <;> cases i <;> unfold splitPart <;> rw [hd] <;>
    first
      | rfl
      | (apply key; rw [hd]; rfl)
      | (cases s <;> first | rfl | (apply key; rw [hd]; rfl))

end Part

/-! ### Fitting a part -/

namespace Hypermap

variable {D : Type*}

/-- `G.Fitp x p` holds when the subparts of the sector `p` describe the second
neighbourhood of `x`, starting at the spoke of `x`: each range of `p` contains
the arity of the face it points at. -/
def Fitp (G : Hypermap D) : D → Part → Prop
  | _, .nil => True
  | x, .cons s h p =>
      s.Mem (G.arity (SubpartLoc.spoke.dart G x)) ∧
        h.Mem (G.arity (SubpartLoc.hat.dart G x)) ∧ Fitp G (G.face x) p
  | x, .cons6 h f1 p =>
      PRange.pr66.Mem (G.arity (SubpartLoc.spoke.dart G x)) ∧
        h.Mem (G.arity (SubpartLoc.hat.dart G x)) ∧
          f1.Mem (G.arity (SubpartLoc.fan1.dart G x)) ∧ Fitp G (G.face x) p
  | x, .cons7 h f1 f2 p =>
      PRange.pr77.Mem (G.arity (SubpartLoc.spoke.dart G x)) ∧
        h.Mem (G.arity (SubpartLoc.hat.dart G x)) ∧
          f1.Mem (G.arity (SubpartLoc.fan1.dart G x)) ∧
            f2.Mem (G.arity (SubpartLoc.fan2.dart G x)) ∧ Fitp G (G.face x) p
  | x, .cons8 h f1 f2 f3 p =>
      PRange.pr88.Mem (G.arity (SubpartLoc.spoke.dart G x)) ∧
        h.Mem (G.arity (SubpartLoc.hat.dart G x)) ∧
          f1.Mem (G.arity (SubpartLoc.fan1.dart G x)) ∧
            f2.Mem (G.arity (SubpartLoc.fan2.dart G x)) ∧
              f3.Mem (G.arity (SubpartLoc.fan3.dart G x)) ∧ Fitp G (G.face x) p

variable (G : Hypermap D)

/-- `x` fits `p` at the hub as well: the hub arity is the size of `p`. -/
def ExactFitp (x : D) (p : Part) : Prop := G.arity x = p.size ∧ G.Fitp x p

/-- `x` fits the sector `p`, and its hub arity lies in the range `u`.  This is
the intermediate notion the reference uses to state the converse of a part. -/
def TightFitp (x : D) (u : PRange) (p : Part) : Prop := u.Mem (G.arity x) ∧ G.Fitp x p

/-- Dropping the first `n` subparts corresponds to turning `n` times around the
hub. -/
theorem fitp_drop (n : ℕ) :
    ∀ {p : Part} {x : D}, G.Fitp x p → G.Fitp (G.face^[n] x) (p.drop n) := by
  induction n with
  | zero => intro p x h; simpa only [Part.drop, Function.iterate_zero_apply] using h
  | succ n ih =>
    intro p x h
    rw [Function.iterate_succ_apply]
    cases p with
    | nil => simp only [Part.drop]; trivial
    | cons s hh p => simp only [Fitp] at h; simpa only [Part.drop] using ih h.2.2
    | cons6 hh f1 p => simp only [Fitp] at h; simpa only [Part.drop] using ih h.2.2.2
    | cons7 hh f1 f2 p => simp only [Fitp] at h; simpa only [Part.drop] using ih h.2.2.2.2
    | cons8 hh f1 f2 f3 p =>
      simp only [Fitp] at h; simpa only [Part.drop] using ih h.2.2.2.2.2

/-- Fitting a concatenation is fitting both sectors, the second one after
turning around the hub. -/
theorem fitp_cat (x : D) (p q : Part) :
    G.Fitp x (p.cat q) ↔ G.Fitp x p ∧ G.Fitp (G.face^[p.size] x) q := by
  induction p generalizing x with
  | nil => simp only [Part.cat, Part.size, Fitp, Function.iterate_zero_apply, true_and]
  | cons s h p ih =>
    simp only [Part.cat, Part.size, Fitp, ih, Function.iterate_succ_apply]
    tauto
  | cons6 h f1 p ih =>
    simp only [Part.cat, Part.size, Fitp, ih, Function.iterate_succ_apply]
    tauto
  | cons7 h f1 f2 p ih =>
    simp only [Part.cat, Part.size, Fitp, ih, Function.iterate_succ_apply]
    tauto
  | cons8 h f1 f2 f3 p ih =>
    simp only [Part.cat, Part.size, Fitp, ih, Function.iterate_succ_apply]
    tauto

/-- Fitting the reverse concatenation. -/
theorem fitp_catrev (x : D) (p q : Part) :
    G.Fitp x (p.catrev q) ↔ G.Fitp x p.rev ∧ G.Fitp (G.face^[p.size] x) q := by
  rw [Part.catrev_eq_cat, fitp_cat, Part.size_rev]

/-- Rotating a part corresponds to moving the anchor around the hub. -/
theorem exact_fitp_rot [Finite D] {n : ℕ} {p : Part} (hn : n ≤ p.size) (x : D) :
    G.ExactFitp x p ↔ G.ExactFitp (G.face^[n] x) (p.rot n) := by
  simp only [ExactFitp, Part.size_rot, G.arity_iterate_face]
  refine and_congr_right fun hx => ?_
  have hx' : G.face^[p.size - n] (G.face^[n] x) = x := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn, ← hx, G.iterate_face_arity]
  have key : G.Fitp x p ↔ G.Fitp x (p.take n) ∧ G.Fitp (G.face^[n] x) (p.drop n) := by
    conv_lhs => rw [← Part.cat_take_drop n p]
    rw [fitp_cat, Part.size_take, min_eq_left hn]
  rw [key, Part.rot, fitp_cat, Part.size_drop, hx', and_comm]

/-- The free part of size `n` fits any dart of a pentagonal map. -/
theorem fitp_free (hG : G.Pentagonal) : ∀ (n : ℕ) (x : D), G.Fitp x (Part.free n)
  | 0, _ => trivial
  | n + 1, x =>
      ⟨(PRange.mem_pr59 _).mpr (hG _), (PRange.mem_pr59 _).mpr (hG _), fitp_free hG n (G.face x)⟩

/-- The free part of the right size fits any dart of a pentagonal map. -/
theorem exact_fitp_free (hG : G.Pentagonal) (x : D) : G.ExactFitp x (Part.free (G.arity x)) :=
  ⟨(Part.size_free _).symm, fitp_free G hG _ x⟩

/-- A dart fitting both parts fits their meet. -/
theorem fitp_meet : ∀ (p q : Part) (x : D), G.Fitp x p → G.Fitp x q →
    G.Fitp x (p.meet q) := by
  intro p
  induction p with
  | nil => intro q x hf _; simpa using hf
  | cons sp hp p ih =>
    intro q x hf hg
    cases q with
    | nil => simpa using hf
    | cons sq hq q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨PRange.mem_meet hf.1 hg.1, PRange.mem_meet hf.2.1 hg.2.1, ih _ _ hf.2.2 hg.2.2⟩
    | cons6 hq f1q q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hg.1, PRange.mem_meet hf.2.1 hg.2.1, hg.2.2.1, ih _ _ hf.2.2 hg.2.2.2⟩
    | cons7 hq f1q f2q q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hg.1, PRange.mem_meet hf.2.1 hg.2.1, hg.2.2.1, hg.2.2.2.1, ih _ _ hf.2.2 hg.2.2.2.2⟩
    | cons8 hq f1q f2q f3q q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hg.1,
        PRange.mem_meet hf.2.1 hg.2.1,
        hg.2.2.1,
        hg.2.2.2.1,
        hg.2.2.2.2.1,
        ih _ _ hf.2.2 hg.2.2.2.2.2⟩
  | cons6 hp f1p p ih =>
    intro q x hf hg
    cases q with
    | nil => simpa using hf
    | cons sq hq q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hf.1, PRange.mem_meet hf.2.1 hg.2.1, hf.2.2.1, ih _ _ hf.2.2.2 hg.2.2⟩
    | cons6 hq f1q q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hf.1,
        PRange.mem_meet hf.2.1 hg.2.1,
        PRange.mem_meet hf.2.2.1 hg.2.2.1,
        ih _ _ hf.2.2.2 hg.2.2.2⟩
    | cons7 hq f1q f2q q => simpa [Part.meet] using hf
    | cons8 hq f1q f2q f3q q => simpa [Part.meet] using hf
  | cons7 hp f1p f2p p ih =>
    intro q x hf hg
    cases q with
    | nil => simpa using hf
    | cons sq hq q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hf.1, PRange.mem_meet hf.2.1 hg.2.1, hf.2.2.1, hf.2.2.2.1, ih _ _ hf.2.2.2.2 hg.2.2⟩
    | cons6 hq f1q q => simpa [Part.meet] using hf
    | cons7 hq f1q f2q q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hf.1,
        PRange.mem_meet hf.2.1 hg.2.1,
        PRange.mem_meet hf.2.2.1 hg.2.2.1,
        PRange.mem_meet hf.2.2.2.1 hg.2.2.2.1,
        ih _ _ hf.2.2.2.2 hg.2.2.2.2⟩
    | cons8 hq f1q f2q f3q q => simpa [Part.meet] using hf
  | cons8 hp f1p f2p f3p p ih =>
    intro q x hf hg
    cases q with
    | nil => simpa using hf
    | cons sq hq q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hf.1,
        PRange.mem_meet hf.2.1 hg.2.1,
        hf.2.2.1,
        hf.2.2.2.1,
        hf.2.2.2.2.1,
        ih _ _ hf.2.2.2.2.2 hg.2.2⟩
    | cons6 hq f1q q => simpa [Part.meet] using hf
    | cons7 hq f1q f2q q => simpa [Part.meet] using hf
    | cons8 hq f1q f2q f3q q =>
      simp only [Fitp] at hf hg ⊢
      simp only [Part.meet, Fitp]
      exact ⟨hf.1,
        PRange.mem_meet hf.2.1 hg.2.1,
        PRange.mem_meet hf.2.2.1 hg.2.2.1,
        PRange.mem_meet hf.2.2.2.1 hg.2.2.2.1,
        PRange.mem_meet hf.2.2.2.2.1 hg.2.2.2.2.1,
        ih _ _ hf.2.2.2.2.2 hg.2.2.2.2.2⟩

/-- A dart exactly fitting `p` and fitting the sector `q` exactly fits their
meet. -/
theorem exact_fitp_meet (p q : Part) (x : D) (hp : G.ExactFitp x p)
    (hq : G.Fitp x q) : G.ExactFitp x (p.meet q) :=
  ⟨by rw [Part.size_meet]; exact hp.1, fitp_meet G p q x hp.2 hq⟩

/-- If `p` is a subset of `q`, every dart fitting `p` fits `q`. -/
theorem fitp_cmp_subset : ∀ (p q : Part) (x : D), p.cmp q = .subset → G.Fitp x p →
    G.Fitp x q := by
  intro p
  induction p with
  | nil =>
    intro q x h hf
    cases q with
    | nil => trivial
    | cons sq hq q => simp [Part.cmp] at h
    | cons6 hq f1q q => simp [Part.cmp] at h
    | cons7 hq f1q f2q q => simp [Part.cmp] at h
    | cons8 hq f1q f2q f3q q => simp [Part.cmp] at h
  | cons sp hp p ih =>
    intro q x h hf
    cases q with
    | nil => trivial
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_subset] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [Fitp] at hf ⊢
      exact ⟨PRange.mem_of_cmp_eq_subset h1 hf.1,
        PRange.mem_of_cmp_eq_subset h2 hf.2.1,
        ih _ _ h3 hf.2.2⟩
    | cons6 hq f1q q => simp [Part.cmp] at h
    | cons7 hq f1q f2q q => simp [Part.cmp] at h
    | cons8 hq f1q f2q f3q q => simp [Part.cmp] at h
  | cons6 hp f1p p ih =>
    intro q x h hf
    cases q with
    | nil => trivial
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_subset] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [Fitp] at hf ⊢
      exact ⟨PRange.mem_of_cmp_eq_subset h1 hf.1,
        PRange.mem_of_cmp_eq_subset h2 hf.2.1,
        ih _ _ h3 hf.2.2.2⟩
    | cons6 hq f1q q =>
      simp only [Part.cmp, PartRel.meet_eq_subset] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [Fitp] at hf ⊢
      exact ⟨hf.1,
        PRange.mem_of_cmp_eq_subset h1 hf.2.1,
        PRange.mem_of_cmp_eq_subset h2 hf.2.2.1,
        ih _ _ h3 hf.2.2.2⟩
    | cons7 hq f1q f2q q => simp [Part.cmp] at h
    | cons8 hq f1q f2q f3q q => simp [Part.cmp] at h
  | cons7 hp f1p f2p p ih =>
    intro q x h hf
    cases q with
    | nil => trivial
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_subset] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [Fitp] at hf ⊢
      exact ⟨PRange.mem_of_cmp_eq_subset h1 hf.1,
        PRange.mem_of_cmp_eq_subset h2 hf.2.1,
        ih _ _ h3 hf.2.2.2.2⟩
    | cons6 hq f1q q => simp [Part.cmp] at h
    | cons7 hq f1q f2q q =>
      simp only [Part.cmp, PartRel.meet_eq_subset] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      simp only [Fitp] at hf ⊢
      exact ⟨hf.1,
        PRange.mem_of_cmp_eq_subset h1 hf.2.1,
        PRange.mem_of_cmp_eq_subset h2 hf.2.2.1,
        PRange.mem_of_cmp_eq_subset h3 hf.2.2.2.1,
        ih _ _ h4 hf.2.2.2.2⟩
    | cons8 hq f1q f2q f3q q => simp [Part.cmp] at h
  | cons8 hp f1p f2p f3p p ih =>
    intro q x h hf
    cases q with
    | nil => trivial
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_subset] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [Fitp] at hf ⊢
      exact ⟨PRange.mem_of_cmp_eq_subset h1 hf.1,
        PRange.mem_of_cmp_eq_subset h2 hf.2.1,
        ih _ _ h3 hf.2.2.2.2.2⟩
    | cons6 hq f1q q => simp [Part.cmp] at h
    | cons7 hq f1q f2q q => simp [Part.cmp] at h
    | cons8 hq f1q f2q f3q q =>
      simp only [Part.cmp, PartRel.meet_eq_subset] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only [Fitp] at hf ⊢
      exact ⟨hf.1,
        PRange.mem_of_cmp_eq_subset h1 hf.2.1,
        PRange.mem_of_cmp_eq_subset h2 hf.2.2.1,
        PRange.mem_of_cmp_eq_subset h3 hf.2.2.2.1,
        PRange.mem_of_cmp_eq_subset h4 hf.2.2.2.2.1,
        ih _ _ h5 hf.2.2.2.2.2⟩

/-- If `p` and `q` are disjoint, no dart fits both. -/
theorem fitp_cmp_disjoint : ∀ (p q : Part) (x : D), p.cmp q = .disjoint → G.Fitp x p →
    ¬ G.Fitp x q := by
  intro p
  induction p with
  | nil => intro q x h hf; cases q <;> simp [Part.cmp] at h
  | cons sp hp p ih =>
    intro q x h hf
    cases q with
    | nil => simp [Part.cmp] at h
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.1 g0
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact ih _ _ h hf.2.2 g2
    | cons6 hq f1q q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint,
        PartRel.notSubset_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2, g3⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.1 g0
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact ih _ _ h hf.2.2 g3
    | cons7 hq f1q f2q q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint,
        PartRel.notSubset_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2, g3, g4⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.1 g0
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact ih _ _ h hf.2.2 g4
    | cons8 hq f1q f2q f3q q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint,
        PartRel.notSubset_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2, g3, g4, g5⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.1 g0
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact ih _ _ h hf.2.2 g5
  | cons6 hp f1p p ih =>
    intro q x h hf
    cases q with
    | nil => simp [Part.cmp] at h
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.1 g0
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact ih _ _ h hf.2.2.2 g2
    | cons6 hq f1q q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2, g3⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.2.1 g2
      · exact ih _ _ h hf.2.2.2 g3
    | cons7 hq f1q f2q q =>
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, -⟩
      exact PRange.not_mem_of_cmp_eq_disjoint (by decide) hf.1 g0
    | cons8 hq f1q f2q f3q q =>
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, -⟩
      exact PRange.not_mem_of_cmp_eq_disjoint (by decide) hf.1 g0
  | cons7 hp f1p f2p p ih =>
    intro q x h hf
    cases q with
    | nil => simp [Part.cmp] at h
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.1 g0
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact ih _ _ h hf.2.2.2.2 g2
    | cons6 hq f1q q =>
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, -⟩
      exact PRange.not_mem_of_cmp_eq_disjoint (by decide) hf.1 g0
    | cons7 hq f1q f2q q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2, g3, g4⟩
      rcases h with h | h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.2.1 g2
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.2.2.1 g3
      · exact ih _ _ h hf.2.2.2.2 g4
    | cons8 hq f1q f2q f3q q =>
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, -⟩
      exact PRange.not_mem_of_cmp_eq_disjoint (by decide) hf.1 g0
  | cons8 hp f1p f2p f3p p ih =>
    intro q x h hf
    cases q with
    | nil => simp [Part.cmp] at h
    | cons sq hq q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2⟩
      rcases h with h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.1 g0
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact ih _ _ h hf.2.2.2.2.2 g2
    | cons6 hq f1q q =>
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, -⟩
      exact PRange.not_mem_of_cmp_eq_disjoint (by decide) hf.1 g0
    | cons7 hq f1q f2q q =>
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, -⟩
      exact PRange.not_mem_of_cmp_eq_disjoint (by decide) hf.1 g0
    | cons8 hq f1q f2q f3q q =>
      simp only [Part.cmp, PartRel.meet_eq_disjoint] at h
      simp only [Fitp] at hf ⊢
      rintro ⟨g0, g1, g2, g3, g4, g5⟩
      rcases h with h | h | h | h | h
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.1 g1
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.2.1 g2
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.2.2.1 g3
      · exact PRange.not_mem_of_cmp_eq_disjoint h hf.2.2.2.2.1 g4
      · exact ih _ _ h hf.2.2.2.2.2 g5

/-- The comparison of two parts predicts the fitting test for the second one,
at any dart fitting the first. -/
theorem fitp_cmp {p : Part} {x : D} (hf : G.Fitp x p) (q : Part) :
    G.Fitp x q ↔ (p.cmp q).Holds (G.Fitp x q) :=
  PartRel.holds_iff (fun h => fitp_cmp_subset G p q x h hf)
    (fun h => fitp_cmp_disjoint G p q x h hf)

/-! #### Valid part constructors and splitting

A part constructor with a hole at a given location adds one subpart, and
changing the range in the hole only changes the arity test at that
location. -/

/-- `G.PartUpdate fc i` : `fc r p` adds one subpart to `p`, and a dart fitting
`fc r p` fits `fc r' p` exactly when the arity at location `i` is in `r'`. -/
structure PartUpdate (fc : PRange → Part → Part) (i : SubpartLoc) : Prop where
  /-- The constructor adds exactly one subpart. -/
  size_eq : ∀ (r : PRange) (p : Part), (fc r p).size = p.size + 1
  /-- Fitting implies the arity test at the hole. -/
  mem_of_fitp : ∀ (r : PRange) (p : Part) (x : D), G.Fitp x (fc r p) →
    r.Mem (G.arity (i.dart G x))
  /-- Any other range passing the test at the hole also fits. -/
  fitp_of_mem : ∀ (r r' : PRange) (p : Part) (x : D), G.Fitp x (fc r p) →
    r'.Mem (G.arity (i.dart G x)) → G.Fitp x (fc r' p)

/-- The constructor with a hole at the spoke of a `cons` subpart. -/
theorem updateSpoke (h : PRange) :
    G.PartUpdate (fun r => Part.cons r h) .spoke :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.1,
    fun _ _ _ _ hx hm => ⟨hm, hx.2.1, hx.2.2⟩⟩

/-- The constructor with a hole at the hat of a `cons` subpart. -/
theorem updateHat (s : PRange) :
    G.PartUpdate (fun r => Part.cons s r) .hat :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hm, hx.2.2⟩⟩

/-- The constructor with a hole at the hat of a `cons6` subpart. -/
theorem update6Hat (f1 : PRange) :
    G.PartUpdate (fun r => Part.cons6 r f1) .hat :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hm, hx.2.2.1, hx.2.2.2⟩⟩

/-- The constructor with a hole at the first fan of a `cons6` subpart. -/
theorem update6Fan1 (h : PRange) :
    G.PartUpdate (fun r => Part.cons6 h r) .fan1 :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hx.2.1, hm, hx.2.2.2⟩⟩

/-- The constructor with a hole at the hat of a `cons7` subpart. -/
theorem update7Hat (f1 f2 : PRange) :
    G.PartUpdate (fun r => Part.cons7 r f1 f2) .hat :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hm, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩⟩

/-- The constructor with a hole at the first fan of a `cons7` subpart. -/
theorem update7Fan1 (h f2 : PRange) :
    G.PartUpdate (fun r => Part.cons7 h r f2) .fan1 :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hx.2.1, hm, hx.2.2.2.1, hx.2.2.2.2⟩⟩

/-- The constructor with a hole at the second fan of a `cons7` subpart. -/
theorem update7Fan2 (h f1 : PRange) :
    G.PartUpdate (fun r => Part.cons7 h f1 r) .fan2 :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.2.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hx.2.1, hx.2.2.1, hm, hx.2.2.2.2⟩⟩

/-- The constructor with a hole at the hat of a `cons8` subpart. -/
theorem update8Hat (f1 f2 f3 : PRange) :
    G.PartUpdate (fun r => Part.cons8 r f1 f2 f3) .hat :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hm, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2⟩⟩

/-- The constructor with a hole at the first fan of a `cons8` subpart. -/
theorem update8Fan1 (h f2 f3 : PRange) :
    G.PartUpdate (fun r => Part.cons8 h r f2 f3) .fan1 :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hx.2.1, hm, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2⟩⟩

/-- The constructor with a hole at the second fan of a `cons8` subpart. -/
theorem update8Fan2 (h f1 f3 : PRange) :
    G.PartUpdate (fun r => Part.cons8 h f1 r f3) .fan2 :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.2.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hx.2.1, hx.2.2.1, hm, hx.2.2.2.2.1, hx.2.2.2.2.2⟩⟩

/-- The constructor with a hole at the third fan of a `cons8` subpart. -/
theorem update8Fan3 (h f1 f2 : PRange) :
    G.PartUpdate (fun r => Part.cons8 h f1 f2 r) .fan3 :=
  ⟨fun _ _ => rfl, fun _ _ _ hx => hx.2.2.2.2.1,
    fun _ _ _ _ hx hm => ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hm, hx.2.2.2.2.2⟩⟩

/-- Splitting the range in the hole of a valid constructor splits fitting
according to the arity at that location. -/
theorem fitp_update_split {fc : PRange → Part → Part} {i : SubpartLoc}
    (hu : G.PartUpdate fc i) {k : ℕ} {r : PRange} (hr : PRange.GoodRSplit k r)
    (lo : Bool) (q : Part) (y : D) :
    G.Fitp y (fc (PRange.splitRange k lo r) q) ↔
      PRange.SplitCond lo k (G.arity (i.dart G y)) ∧ G.Fitp y (fc r q) := by
  constructor
  · intro hfit
    have h1 := hu.mem_of_fitp _ _ _ hfit
    rw [PRange.mem_splitRange hr] at h1
    exact ⟨h1.1, hu.fitp_of_mem _ _ _ _ hfit h1.2⟩
  · rintro ⟨hc, hfit⟩
    have h1 := hu.mem_of_fitp _ _ _ hfit
    exact hu.fitp_of_mem _ _ _ _ hfit ((PRange.mem_splitRange hr lo _).mpr ⟨hc, h1⟩)

/-- The generic step of `fitp_split`: replacing the subpart `j` of `p` by a
constructor with a split range. -/
theorem fitp_split_aux {fc : PRange → Part → Part} {i : SubpartLoc}
    (hu : G.PartUpdate fc i) {k : ℕ} {r : PRange} (hr : PRange.GoodRSplit k r)
    (lo : Bool) {j : ℕ} {p q : Part} (x : D)
    (hsize : (p.drop j).size = (fc r q).size)
    (hfit : ∀ y : D, G.Fitp y (p.drop j) ↔ G.Fitp y (fc r q)) :
    G.Fitp x ((p.take j).cat (fc (PRange.splitRange k lo r) q)) ↔
      PRange.SplitCond lo k (G.arity (i.dart G (G.face^[j] x))) ∧ G.Fitp x p := by
  have hj : j ≤ p.size := by
    have h1 : (p.drop j).size = p.size - j := Part.size_drop j p
    rw [hsize, hu.size_eq] at h1
    omega
  have htake : (p.take j).size = j := by rw [Part.size_take, min_eq_left hj]
  have hp : G.Fitp x p ↔ G.Fitp x (p.take j) ∧ G.Fitp (G.face^[j] x) (fc r q) := by
    conv_lhs => rw [← Part.cat_take_drop j p]
    rw [fitp_cat, htake, hfit]
  rw [fitp_cat, htake, hp, fitp_update_split G hu hr lo q (G.face^[j] x)]
  tauto

/-- Fitting a split part: the dart fits the half selected by its arity at the
split location. -/
theorem fitp_split (hG : G.Pentagonal) (i : SubpartLoc) (j k : ℕ) (p : Part)
    (hgs : Part.GoodSplit i j k p) (lo : Bool) (x : D) :
    G.Fitp x (Part.splitPart i j k lo p) ↔
      PRange.SplitCond lo k (G.arity (i.dart G (G.face^[j] x))) ∧ G.Fitp x p := by
  unfold Part.GoodSplit at hgs
  unfold Part.splitPart
  have m : ∀ z : D, PRange.pr59.Mem (G.arity z) := fun z => (PRange.mem_pr59 _).mpr (hG z)
  rcases hd : p.drop j with _ | ⟨s, hh, p'⟩ | ⟨hh, f1, p'⟩ | ⟨hh, f1, f2, p'⟩ |
    ⟨hh, f1, f2, f3, p'⟩ <;> rw [hd] at hgs
  · -- the sector is empty: no split is possible
    cases i <;> exact (hgs : False).elim
  · -- the subpart `j` is a `cons`
    cases i with
    | spoke =>
      exact fitp_split_aux G (G.updateSpoke hh) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | hat =>
      exact fitp_split_aux G (G.updateHat s) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan1 =>
      cases s
      case pr66 =>
        exact fitp_split_aux G (G.update6Fan1 hh) hgs lo x
          (by simp only [hd, Part.size])
          (by
            rw [hd]
            intro y
            simp only [Fitp]
            exact ⟨fun hy => ⟨hy.1, hy.2.1, m _, hy.2.2⟩,
              fun hy => ⟨hy.1, hy.2.1, hy.2.2.2⟩⟩)
      case pr77 =>
        exact fitp_split_aux G (G.update7Fan1 hh .pr59) hgs lo x
          (by simp only [hd, Part.size])
          (by
            rw [hd]
            intro y
            simp only [Fitp]
            exact ⟨fun hy => ⟨hy.1, hy.2.1, m _, m _, hy.2.2⟩,
              fun hy => ⟨hy.1, hy.2.1, hy.2.2.2.2⟩⟩)
      case pr88 =>
        exact fitp_split_aux G (G.update8Fan1 hh .pr59 .pr59) hgs lo x
          (by simp only [hd, Part.size])
          (by
            rw [hd]
            intro y
            simp only [Fitp]
            exact ⟨fun hy => ⟨hy.1, hy.2.1, m _, m _, m _, hy.2.2⟩,
              fun hy => ⟨hy.1, hy.2.1, hy.2.2.2.2.2⟩⟩)
      all_goals exact (hgs : False).elim
    | fan2 =>
      cases s
      case pr77 =>
        exact fitp_split_aux G (G.update7Fan2 hh .pr59) hgs lo x
          (by simp only [hd, Part.size])
          (by
            rw [hd]
            intro y
            simp only [Fitp]
            exact ⟨fun hy => ⟨hy.1, hy.2.1, m _, m _, hy.2.2⟩,
              fun hy => ⟨hy.1, hy.2.1, hy.2.2.2.2⟩⟩)
      case pr88 =>
        exact fitp_split_aux G (G.update8Fan2 hh .pr59 .pr59) hgs lo x
          (by simp only [hd, Part.size])
          (by
            rw [hd]
            intro y
            simp only [Fitp]
            exact ⟨fun hy => ⟨hy.1, hy.2.1, m _, m _, m _, hy.2.2⟩,
              fun hy => ⟨hy.1, hy.2.1, hy.2.2.2.2.2⟩⟩)
      all_goals exact (hgs : False).elim
    | fan3 =>
      cases s
      case pr88 =>
        exact fitp_split_aux G (G.update8Fan3 hh .pr59 .pr59) hgs lo x
          (by simp only [hd, Part.size])
          (by
            rw [hd]
            intro y
            simp only [Fitp]
            exact ⟨fun hy => ⟨hy.1, hy.2.1, m _, m _, m _, hy.2.2⟩,
              fun hy => ⟨hy.1, hy.2.1, hy.2.2.2.2.2⟩⟩)
      all_goals exact (hgs : False).elim
  · -- the subpart `j` is a `cons6`
    cases i with
    | spoke => exact (hgs : False).elim
    | hat =>
      exact fitp_split_aux G (G.update6Hat f1) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan1 =>
      exact fitp_split_aux G (G.update6Fan1 hh) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan2 => exact (hgs : False).elim
    | fan3 => exact (hgs : False).elim
  · -- the subpart `j` is a `cons7`
    cases i with
    | spoke => exact (hgs : False).elim
    | hat =>
      exact fitp_split_aux G (G.update7Hat f1 f2) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan1 =>
      exact fitp_split_aux G (G.update7Fan1 hh f2) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan2 =>
      exact fitp_split_aux G (G.update7Fan2 hh f1) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan3 => exact (hgs : False).elim
  · -- the subpart `j` is a `cons8`
    cases i with
    | spoke => exact (hgs : False).elim
    | hat =>
      exact fitp_split_aux G (G.update8Hat f1 f2 f3) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan1 =>
      exact fitp_split_aux G (G.update8Fan1 hh f2 f3) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan2 =>
      exact fitp_split_aux G (G.update8Fan2 hh f1 f3) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)
    | fan3 =>
      exact fitp_split_aux G (G.update8Fan3 hh f1 f2) hgs lo x
        (by simp only [hd, Part.size])
        (by rw [hd]; exact fun y => Iff.rfl)

/-- Exact fitting of a split part. -/
theorem exact_fitp_split (hG : G.Pentagonal) (i : SubpartLoc) (j k : ℕ) (p : Part)
    (hgs : Part.GoodSplit i j k p) (lo : Bool) (x : D) :
    G.ExactFitp x (Part.splitPart i j k lo p) ↔
      PRange.SplitCond lo k (G.arity (i.dart G (G.face^[j] x))) ∧ G.ExactFitp x p := by
  rw [ExactFitp, ExactFitp, Part.size_splitPart, fitp_split G hG i j k p hgs lo x]
  tauto

/-! ### Fitting the mirror image

The remaining fitting theorems depend on the geometry of the hypermap.  The
mirror image of a part fits a dart exactly when the part fits that dart in the
mirror hypermap; this needs plainness and cubicity, but not pentagonality. -/

/-- The arity of the face across the `n`-th edge counterclockwise from the
spoke of `x`.  The hat and the three fans of the first subpart at `x` are the
locations `n = 2, 3, 4, 5`; the spoke itself is not of this form. -/
noncomputable def ars (n : ℕ) (x : D) : ℕ := G.arity (G.edge (G.face^[n] (G.edge x)))

/-- Fitting a subpart with a free spoke, in terms of `Hypermap.ars`. -/
theorem fitp_cons (s h : PRange) (q : Part) (x : D) :
    G.Fitp x (.cons s h q) ↔
      s.Mem (G.arity (G.edge x)) ∧ h.Mem (G.ars 2 x) ∧ G.Fitp (G.face x) q := Iff.rfl

/-- Fitting a subpart with one known fan, in terms of `Hypermap.ars`. -/
theorem fitp_cons6 (h f1 : PRange) (q : Part) (x : D) :
    G.Fitp x (.cons6 h f1 q) ↔
      PRange.pr66.Mem (G.arity (G.edge x)) ∧ h.Mem (G.ars 2 x) ∧ f1.Mem (G.ars 3 x) ∧
        G.Fitp (G.face x) q := Iff.rfl

/-- Fitting a subpart with two known fans, in terms of `Hypermap.ars`. -/
theorem fitp_cons7 (h f1 f2 : PRange) (q : Part) (x : D) :
    G.Fitp x (.cons7 h f1 f2 q) ↔
      PRange.pr77.Mem (G.arity (G.edge x)) ∧ h.Mem (G.ars 2 x) ∧ f1.Mem (G.ars 3 x) ∧
        f2.Mem (G.ars 4 x) ∧ G.Fitp (G.face x) q := Iff.rfl

/-- Fitting a subpart with three known fans, in terms of `Hypermap.ars`. -/
theorem fitp_cons8 (h f1 f2 f3 : PRange) (q : Part) (x : D) :
    G.Fitp x (.cons8 h f1 f2 f3 q) ↔
      PRange.pr88.Mem (G.arity (G.edge x)) ∧ h.Mem (G.ars 2 x) ∧ f1.Mem (G.ars 3 x) ∧
        f2.Mem (G.ars 4 x) ∧ f3.Mem (G.ars 5 x) ∧ G.Fitp (G.face x) q := Iff.rfl

/-- The hat range of a nonempty sector is met at the base dart of a fit. -/
theorem fitp_hat (h' : PRange) {x : D} :
    ∀ {q : Part}, G.Fitp x q → q ≠ .nil → (Part.nextHat h' q).Mem (G.ars 2 x)
  | .nil, _, hne => absurd rfl hne
  | .cons _ _ _, hf, _ => hf.2.1
  | .cons6 _ _ _, hf, _ => hf.2.1
  | .cons7 _ _ _ _, hf, _ => hf.2.1
  | .cons8 _ _ _ _ _, hf, _ => hf.2.1

/-! #### The three mirror computations -/

/-- The edge permutation of the mirror hypermap, pointwise. -/
theorem mirror_edge_apply (x : D) : G.mirror.edge x = G.face (G.node x) := rfl

/-- The face permutation of the mirror hypermap, pointwise. -/
theorem mirror_face_apply (x : D) : G.mirror.face x = G.edge (G.node x) := by
  rw [Hypermap.mirror_face]
  exact Equiv.Perm.inv_eq_iff_eq.mpr (G.nodeK x).symm

/-- The mirror face permutation undoes the face permutation. -/
theorem mirror_face_face (x : D) : G.mirror.face (G.face x) = x := by
  rw [Hypermap.mirror_face]
  exact Equiv.Perm.inv_eq_iff_eq.mpr rfl

/-- Turning back around a face. -/
theorem arity_edge_node [Finite D] (x : D) : G.arity (G.edge (G.node x)) = G.arity x := by
  have h := G.arity_face (G.edge (G.node x))
  rw [G.nodeK] at h
  exact h.symm

/-- Undoing an iterated face step. -/
theorem iterate_faceInv_iterate_face (k : ℕ) (z : D) :
    (⇑(G.face⁻¹ : Equiv.Perm D))^[k] (G.face^[k] z) = z := by
  have hinv : ∀ w : D, (G.face⁻¹ : Equiv.Perm D) (G.face w) = w :=
    fun _ => Equiv.Perm.inv_eq_iff_eq.mpr rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', hinv]
    exact ih

/-- The spoke computation: the mirror spoke at `face x` is the spoke at `x`. -/
theorem arity_mirror_edge_face [Finite D] (hp : G.Plain) (x : D) :
    G.mirror.arity (G.mirror.edge (G.face x)) = G.arity (G.edge x) := by
  rw [G.arity_mirror, mirror_edge_apply, hp.node_face, G.arity_face]

/-- The hat computation: the hat is the same in the mirror hypermap. -/
theorem ars_two_mirror [Finite D] (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.mirror.ars 2 x = G.ars 2 x := by
  have hef : ∀ y : D, G.node (G.node (G.edge y)) = G.face y := by
    intro y; rw [hc.node_node, hp.edge_edge]
  have key : G.mirror.ars 2 x = G.arity (G.node (G.edge (G.node (G.node x)))) := by
    change G.mirror.arity
      (G.mirror.edge (G.mirror.face (G.mirror.face (G.mirror.edge x)))) = _
    rw [G.arity_mirror, mirror_edge_apply, mirror_face_apply, mirror_face_apply,
      mirror_edge_apply, hp.node_face, hp.edge_edge, G.arity_face]
  have key2 : G.ars 2 x
      = G.arity (G.edge (G.node (G.node (G.edge (G.node (G.node x)))))) := by
    change G.arity (G.edge (G.face (G.face (G.edge x)))) = _
    rw [← hef, ← hef, hp.edge_edge]
  rw [key, key2, arity_edge_node]

/-- The fan computation: the fans are reversed in the mirror hypermap. -/
theorem ars_mirror_face [Finite D] (hp : G.Plain) (x : D) {m n : ℕ}
    (hm : G.arity (G.edge x) = m) (hnm : n ≤ m) :
    G.mirror.ars n (G.face x) = G.ars (m - n) x := by
  have h1 : G.face^[n] (G.face^[m - n] (G.edge x)) = G.edge x := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hnm, ← hm, G.iterate_face_arity]
  have h3 : G.face^[n] (G.face (G.face^[m - n] (G.edge x))) = G.face (G.edge x) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', h1]
  have h2 : (⇑(G.face⁻¹ : Equiv.Perm D))^[n] (G.face (G.edge x))
      = G.face (G.face^[m - n] (G.edge x)) := by
    conv_lhs => rw [← h3]
    rw [iterate_faceInv_iterate_face]
  change G.mirror.arity (G.mirror.edge (G.mirror.face^[n] (G.mirror.edge (G.face x)))) = _
  rw [G.arity_mirror, mirror_edge_apply, mirror_edge_apply, hp.node_face,
    Hypermap.mirror_face, h2, hp.node_face, G.arity_face]
  rfl

/-! #### The mirror fitting theorem -/

/-- The inductive form of `Hypermap.fitp_mirror`: the mirror image of the
sector `p` fits `x` in `G`, together with the hat that wraps around at the
far end, exactly when `p` fits the far end of the sector in the mirror
hypermap, together with the hat that wraps around at `x`. -/
theorem fitp_mirrorRec [Finite D] (hp : G.Plain) (hc : G.Cubic) (h0 : PRange) :
    ∀ (p : Part) (x : D),
      (G.Fitp x (Part.mirrorRec h0 .nil p) ∧
          (Part.nextHat h0 p).Mem (G.ars 2 (G.face^[p.size] x))) ↔
        (G.mirror.Fitp (G.face^[p.size] x) p ∧ h0.Mem (G.ars 2 x)) := by
  have hnil : ∀ y : D, G.Fitp y .nil := fun _ => True.intro
  intro p
  induction p with
  | nil => intro x; exact Iff.rfl
  | cons s hh p ih =>
    intro x
    have hcat : Part.mirrorRec h0 .nil (.cons s hh p)
        = Part.cat (Part.mirrorRec h0 .nil p) (.cons s (Part.nextHat h0 p) .nil) := by
      change Part.mirrorRec h0 (.cons s (Part.nextHat h0 p) .nil) p = _
      exact Part.mirrorRec_eq_cat _ _ _
    have hsz : (Part.mirrorRec h0 .nil p).size = p.size := by
      simp [Part.size_mirrorRec, Part.size]
    have hit : G.face^[(Part.cons s hh p).size] x = G.face (G.face^[p.size] x) := by
      change G.face^[p.size + 1] x = _
      exact Function.iterate_succ_apply' _ _ _
    have IH := ih x
    rw [hcat, G.fitp_cat, hsz, hit]
    simp only [Part.nextHat]
    rw [G.fitp_cons, G.mirror.fitp_cons, arity_mirror_edge_face G hp,
      ars_two_mirror G hp hc, mirror_face_face]
    tauto
  | cons6 hh f1 p ih =>
    intro x
    have hcat : Part.mirrorRec h0 .nil (.cons6 hh f1 p)
        = Part.cat (Part.mirrorRec h0 .nil p) (.cons6 (Part.nextHat h0 p) f1 .nil) := by
      change Part.mirrorRec h0 (.cons6 (Part.nextHat h0 p) f1 .nil) p = _
      exact Part.mirrorRec_eq_cat _ _ _
    have hsz : (Part.mirrorRec h0 .nil p).size = p.size := by
      simp [Part.size_mirrorRec, Part.size]
    have hit : G.face^[(Part.cons6 hh f1 p).size] x = G.face (G.face^[p.size] x) := by
      change G.face^[p.size + 1] x = _
      exact Function.iterate_succ_apply' _ _ _
    have IH := ih x
    rw [hcat, G.fitp_cat, hsz, hit]
    simp only [Part.nextHat]
    rw [G.fitp_cons6, G.mirror.fitp_cons6, arity_mirror_edge_face G hp,
      ars_two_mirror G hp hc, mirror_face_face]
    by_cases h6 : G.arity (G.edge (G.face^[p.size] x)) = 6
    · have e1 : G.mirror.ars 3 (G.face (G.face^[p.size] x)) = G.ars 3 (G.face^[p.size] x) := by
        simpa using ars_mirror_face G hp _ h6 (by norm_num : (3 : ℕ) ≤ 6)
      rw [e1]; tauto
    · have h6' : ¬ PRange.pr66.Mem (G.arity (G.edge (G.face^[p.size] x))) := by
        rw [PRange.mem_pr66]; exact h6
      tauto
  | cons7 hh f1 f2 p ih =>
    intro x
    have hcat : Part.mirrorRec h0 .nil (.cons7 hh f1 f2 p)
        = Part.cat (Part.mirrorRec h0 .nil p) (.cons7 (Part.nextHat h0 p) f2 f1 .nil) := by
      change Part.mirrorRec h0 (.cons7 (Part.nextHat h0 p) f2 f1 .nil) p = _
      exact Part.mirrorRec_eq_cat _ _ _
    have hsz : (Part.mirrorRec h0 .nil p).size = p.size := by
      simp [Part.size_mirrorRec, Part.size]
    have hit : G.face^[(Part.cons7 hh f1 f2 p).size] x = G.face (G.face^[p.size] x) := by
      change G.face^[p.size + 1] x = _
      exact Function.iterate_succ_apply' _ _ _
    have IH := ih x
    rw [hcat, G.fitp_cat, hsz, hit]
    simp only [Part.nextHat]
    rw [G.fitp_cons7, G.mirror.fitp_cons7, arity_mirror_edge_face G hp,
      ars_two_mirror G hp hc, mirror_face_face]
    by_cases h7 : G.arity (G.edge (G.face^[p.size] x)) = 7
    · have e1 : G.mirror.ars 3 (G.face (G.face^[p.size] x)) = G.ars 4 (G.face^[p.size] x) := by
        simpa using ars_mirror_face G hp _ h7 (by norm_num : (3 : ℕ) ≤ 7)
      have e2 : G.mirror.ars 4 (G.face (G.face^[p.size] x)) = G.ars 3 (G.face^[p.size] x) := by
        simpa using ars_mirror_face G hp _ h7 (by norm_num : (4 : ℕ) ≤ 7)
      rw [e1, e2]; tauto
    · have h7' : ¬ PRange.pr77.Mem (G.arity (G.edge (G.face^[p.size] x))) := by
        rw [PRange.mem_pr77]; exact h7
      tauto
  | cons8 hh f1 f2 f3 p ih =>
    intro x
    have hcat : Part.mirrorRec h0 .nil (.cons8 hh f1 f2 f3 p)
        = Part.cat (Part.mirrorRec h0 .nil p) (.cons8 (Part.nextHat h0 p) f3 f2 f1 .nil) := by
      change Part.mirrorRec h0 (.cons8 (Part.nextHat h0 p) f3 f2 f1 .nil) p = _
      exact Part.mirrorRec_eq_cat _ _ _
    have hsz : (Part.mirrorRec h0 .nil p).size = p.size := by
      simp [Part.size_mirrorRec, Part.size]
    have hit : G.face^[(Part.cons8 hh f1 f2 f3 p).size] x = G.face (G.face^[p.size] x) := by
      change G.face^[p.size + 1] x = _
      exact Function.iterate_succ_apply' _ _ _
    have IH := ih x
    rw [hcat, G.fitp_cat, hsz, hit]
    simp only [Part.nextHat]
    rw [G.fitp_cons8, G.mirror.fitp_cons8, arity_mirror_edge_face G hp,
      ars_two_mirror G hp hc, mirror_face_face]
    by_cases h8 : G.arity (G.edge (G.face^[p.size] x)) = 8
    · have e1 : G.mirror.ars 3 (G.face (G.face^[p.size] x)) = G.ars 5 (G.face^[p.size] x) := by
        simpa using ars_mirror_face G hp _ h8 (by norm_num : (3 : ℕ) ≤ 8)
      have e2 : G.mirror.ars 4 (G.face (G.face^[p.size] x)) = G.ars 4 (G.face^[p.size] x) := by
        simpa using ars_mirror_face G hp _ h8 (by norm_num : (4 : ℕ) ≤ 8)
      have e3 : G.mirror.ars 5 (G.face (G.face^[p.size] x)) = G.ars 3 (G.face^[p.size] x) := by
        simpa using ars_mirror_face G hp _ h8 (by norm_num : (5 : ℕ) ≤ 8)
      rw [e1, e2, e3]; tauto
    · have h8' : ¬ PRange.pr88.Mem (G.arity (G.edge (G.face^[p.size] x))) := by
        rw [PRange.mem_pr88]; exact h8
      tauto

/-- A dart fits the mirror image of a part exactly when it fits the part in the
mirror hypermap. -/
theorem fitp_mirror [Finite D] (hp : G.Plain) (hc : G.Cubic) (x : D) (p : Part) :
    G.ExactFitp x p.mirror ↔ G.mirror.ExactFitp x p := by
  rw [ExactFitp, ExactFitp, Part.size_mirror, G.arity_mirror]
  refine and_congr_right fun hsz => ?_
  have hfx : G.face^[p.size] x = x := by rw [← hsz, G.iterate_face_arity]
  have key := fitp_mirrorRec G hp hc p.hat p x
  rw [hfx, show Part.nextHat p.hat p = p.hat from by cases p <;> rfl] at key
  by_cases hnil : p = .nil
  · subst hnil; exact Iff.rfl
  · have h1 : G.Fitp x p.mirror → p.hat.Mem (G.ars 2 x) := fun hf => by
      rw [← Part.hat_mirror hnil]
      exact fitp_hat G _ hf (Part.mirror_ne_nil hnil)
    have h2 : G.mirror.Fitp x p → p.hat.Mem (G.ars 2 x) := fun hf => by
      have h := fitp_hat G.mirror PRange.pr59 hf hnil
      rwa [ars_two_mirror G hp hc] at h
    exact ⟨fun hf => (key.mp ⟨hf, h1 hf⟩).1, fun hf => (key.mpr ⟨hf, h2 hf⟩).1⟩

/-- A part contained in its own mirror image fits the same darts in a hypermap
and in its mirror image. -/
theorem fitp_sym [Finite D] (hp : G.Plain) (hc : G.Cubic) {p : Part}
    (hsym : p.cmp p.mirror = .subset) (x : D) :
    G.mirror.ExactFitp x p ↔ G.ExactFitp x p := by
  constructor
  · rintro ⟨hsz, hf⟩
    have hfm : G.mirror.Fitp x p.mirror := by
      have h := fitp_cmp G.mirror hf p.mirror
      rw [hsym] at h
      exact h.mpr trivial
    have h := (fitp_mirror G hp hc x p.mirror).mpr ⟨by rw [Part.size_mirror]; exact hsz, hfm⟩
    rwa [Part.mirror_mirror] at h
  · rintro ⟨hsz, hf⟩
    have hfm : G.Fitp x p.mirror := by
      have h := fitp_cmp G hf p.mirror
      rw [hsym] at h
      exact h.mpr trivial
    exact (fitp_mirror G hp hc x p).mp ⟨by rw [Part.size_mirror]; exact hsz, hfm⟩

/-! ### Fitting the converse part

The converse of a part describes the second neighbourhood of the third spoke
of the hub, read from the dart `Hypermap.invFace2 (G.edge (G.face^[2] x))`.
The lemmas below are the geometric identities this needs; they all hold in a
plain cubic hypermap. -/

/-- Two face steps backwards, written without inverses: `invFace2 x` is
`face⁻¹ (face⁻¹ x)`. -/
def invFace2 (x : D) : D := G.edge (G.node (G.edge (G.node x)))

/-- In a plain cubic hypermap `node (node (edge y)) = face y`. -/
theorem node_node_edge (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.node (G.node (G.edge y)) = G.face y := by
  rw [hc.node_node, hp.edge_edge]

/-- In a plain cubic hypermap `face (edge y) = node (node y)`. -/
theorem face_edge_of_cubic (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.face (G.edge y) = G.node (G.node y) := by
  rw [← node_node_edge G hp hc, hp.edge_edge]

/-- Crossing the edge just after a spoke lands one step back on the previous
spoke. -/
theorem face_edge_face (hp : G.Plain) (hc : G.Cubic) (v : D) :
    G.face (G.edge (G.face v)) = G.node (G.edge v) := by
  rw [face_edge_of_cubic G hp hc, hp.node_face]

/-- The face across the edge following a spoke is the previous spoke. -/
theorem arity_edge_face_edge_face [Finite D] (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.arity (G.edge (G.face (G.edge (G.face y)))) = G.arity (G.edge y) := by
  rw [face_edge_of_cubic G hp hc, hp.node_face, arity_edge_node]

/-- The dart before `u` on its face. -/
theorem iterate_face_pred [Finite D] (u : D) {m : ℕ} (hm : G.arity u = m) (h1 : 1 ≤ m) :
    G.face^[m - 1] u = G.edge (G.node u) := by
  have hmm : m - 1 + 1 = m := Nat.sub_add_cancel h1
  have h : G.face (G.face^[m - 1] u) = G.face (G.edge (G.node u)) := by
    rw [G.nodeK, ← Function.iterate_succ_apply' (G.face : D → D) (m - 1) u,
      Nat.succ_eq_add_one, hmm, ← hm,
      G.iterate_face_arity]
  exact G.face.injective h

/-- The hat of a subpart, seen from the previous spoke: it is the last face
but one around that spoke. -/
theorem arity_hat_prev [Finite D] (hp : G.Plain) (hc : G.Cubic) (v : D) {m : ℕ}
    (hm : G.arity (G.edge v) = m) (h2 : 2 ≤ m) :
    G.arity (G.edge (G.face^[2] (G.edge (G.face v))))
      = G.arity (G.edge (G.face^[m - 2] (G.edge v))) := by
  have hu : G.edge (G.face (G.face^[m - 2] (G.edge v))) = G.node (G.edge v) := by
    rw [← Function.iterate_succ_apply' (G.face : D → D) (m - 2) (G.edge v),
      Nat.succ_eq_add_one, show m - 2 + 1 = m - 1 by omega,
      iterate_face_pred G _ hm (by omega), hp.edge_edge]
  have h1 : G.face^[2] (G.edge (G.face v))
      = G.face (G.edge (G.face (G.face^[m - 2] (G.edge v)))) := by
    change G.face (G.face (G.edge (G.face v))) = _
    rw [face_edge_face G hp hc, ← hu]
  rw [h1, arity_edge_face_edge_face G hp hc]

/-- Two face steps back is `arity - 2` face steps forward. -/
theorem invFace2_eq_iterate [Finite D] (y : D) (h2 : 2 ≤ G.arity y) :
    G.invFace2 y = G.face^[G.arity y - 2] y := by
  have h1 : G.face^[2] (G.invFace2 y) = y := by
    change G.face (G.face (G.invFace2 y)) = y
    simp only [invFace2]; rw [G.nodeK, G.nodeK]
  have h3 : G.face^[2] (G.face^[G.arity y - 2] y) = y := by
    rw [← Function.iterate_add_apply, show 2 + (G.arity y - 2) = G.arity y by omega,
      G.iterate_face_arity]
  exact (G.face.injective.iterate 2) (h1.trans h3.symm)

/-! #### The fourth sector of the converse part -/

/-- `Part.convPart4` produces the subpart of the converse part that describes
the second spoke of the hub, together with the range of the hat that follows
it. -/
theorem fitp_convPart4 [Finite D] (hp : G.Plain) (hc : G.Cubic) (hG : G.Pentagonal)
    (x : D) : ∀ p1 : Part, G.Fitp x p1 →
    (Part.convPart4 p1).1.Mem (G.ars 2 (G.face^[2] (G.edge (G.face^[2] x)))) ∧
      ∀ q5 : Part, G.Fitp (G.face^[2] (G.edge (G.face^[2] x))) q5 →
        G.Fitp (G.face (G.edge (G.face^[2] x))) ((Part.convPart4 p1).2 q5) := by
  have hp59 : ∀ y : D, PRange.pr59.Mem (G.arity y) := fun y => (PRange.mem_pr59 _).mpr (hG y)
  have hE : G.edge (G.face (G.edge (G.face^[2] x)))
      = G.edge (G.node (G.edge (G.face x))) := by
    have h1 : G.face (G.edge (G.face^[2] x)) = G.node (G.node (G.face^[2] x)) :=
      face_edge_of_cubic G hp hc _
    have h2 : G.node (G.face^[2] x) = G.edge (G.face x) := by
      rw [show G.face^[2] x = G.face (G.face x) from rfl, hp.node_face]
    rw [h1, h2]
  have hEf : G.face (G.edge (G.face (G.edge (G.face^[2] x)))) = G.edge (G.face x) := by
    rw [hE, G.nodeK]
  have G1 : G.arity (G.edge (G.face (G.edge (G.face^[2] x))))
      = G.arity (G.edge (G.face x)) := by rw [hE, arity_edge_node]
  have G3 : ∀ j : ℕ, G.ars (j + 1) (G.face (G.edge (G.face^[2] x))) = G.ars j (G.face x) := by
    intro j
    change G.arity (G.edge (G.face^[j + 1]
      (G.edge (G.face (G.edge (G.face^[2] x)))))) = _
    rw [Function.iterate_succ_apply, hEf]
    rfl
  have G2 : G.ars 2 (G.face (G.edge (G.face^[2] x))) = G.arity (G.edge x) := by
    have h := G3 1
    rw [show (1 : ℕ) + 1 = 2 from rfl] at h
    rw [h]
    exact arity_edge_face_edge_face G hp hc x
  have hM : 5 ≤ G.arity (G.edge (G.face x)) := hG _
  have G4 : G.ars 2 (G.face^[2] (G.edge (G.face^[2] x)))
      = G.arity (G.edge (G.face^[G.arity (G.edge (G.face x)) - 3] (G.edge (G.face x)))) := by
    have hhat := arity_hat_prev G hp hc (G.face (G.edge (G.face^[2] x))) G1 (by omega)
    have hstep : G.face^[G.arity (G.edge (G.face x)) - 2]
          (G.edge (G.face (G.edge (G.face^[2] x))))
        = G.face^[G.arity (G.edge (G.face x)) - 3] (G.edge (G.face x)) := by
      rw [show G.arity (G.edge (G.face x)) - 2 = G.arity (G.edge (G.face x)) - 3 + 1 by omega,
        Function.iterate_succ_apply, hEf]
    rw [← hstep, ← hhat]
    rfl
  -- transport lemmas for the three kinds of range test
  have Espoke : ∀ r : PRange, r.Mem (G.arity (G.edge (G.face x))) →
      r.Mem (G.arity (G.edge (G.face (G.edge (G.face^[2] x))))) := by
    intro r h; rw [G1]; exact h
  have Ehat : ∀ r : PRange, r.Mem (G.arity (G.edge x)) →
      r.Mem (G.ars 2 (G.face (G.edge (G.face^[2] x)))) := by
    intro r h; rw [G2]; exact h
  have Efan : ∀ (r : PRange) (j : ℕ), r.Mem (G.ars j (G.face x)) →
      r.Mem (G.ars (j + 1) (G.face (G.edge (G.face^[2] x)))) := by
    intro r j h; rw [G3]; exact h
  have hdef : PRange.pr59.Mem (G.ars 2 (G.face^[2] (G.edge (G.face^[2] x)))) ∧
      ∀ q5 : Part, G.Fitp (G.face^[2] (G.edge (G.face^[2] x))) q5 →
        G.Fitp (G.face (G.edge (G.face^[2] x))) .nil := ⟨hp59 _, fun _ _ => trivial⟩
  intro p1 hfit
  cases p1 with
  | nil => exact hdef
  | cons6 h f1 p => exact hdef
  | cons7 h f1 f2 p => exact hdef
  | cons8 h f1 f2 f3 p => exact hdef
  | cons h34 hh p2 =>
    have Eh34 : h34.Mem (G.arity (G.edge x)) := hfit.1
    have fit2 : G.Fitp (G.face x) p2 := hfit.2.2
    cases p2 with
    | nil => exact hdef
    | cons8 h f1 f2 f3 p => exact hdef
    | cons s4 f41 p =>
      have Es4 : s4.Mem (G.arity (G.edge (G.face x))) := fit2.1
      have Ef41 : f41.Mem (G.ars 2 (G.face x)) := fit2.2.1
      cases f41 <;> cases s4 <;>
        first
          | exact ⟨hp59 _, fun q5 hq => ⟨Espoke _ Es4, Ehat _ Eh34, hq⟩⟩
          | exact ⟨by rw [G4, (PRange.mem_pr55 _).mp Es4]; exact Ef41,
              fun q5 hq => ⟨Espoke _ Es4, Ehat _ Eh34, hq⟩⟩
          | exact ⟨hp59 _, fun q5 hq => ⟨Espoke _ Es4, Ehat _ Eh34, Efan _ 2 Ef41, hq⟩⟩
          | exact ⟨hp59 _,
              fun q5 hq => ⟨Espoke _ Es4, Ehat _ Eh34, Efan _ 2 Ef41, hp59 _, hq⟩⟩
          | exact hdef
    | cons6 f41 h45 p =>
      have Es4 : PRange.pr66.Mem (G.arity (G.edge (G.face x))) := fit2.1
      have Ef41 : f41.Mem (G.ars 2 (G.face x)) := fit2.2.1
      have Eh45 : h45.Mem (G.ars 3 (G.face x)) := fit2.2.2.1
      exact ⟨by rw [G4, (PRange.mem_pr66 _).mp Es4]; exact Eh45,
        fun q5 hq => ⟨Espoke _ Es4, Ehat _ Eh34, Efan _ 2 Ef41, hq⟩⟩
    | cons7 f41 f42 h45 p =>
      have Es4 : PRange.pr77.Mem (G.arity (G.edge (G.face x))) := fit2.1
      have Ef41 : f41.Mem (G.ars 2 (G.face x)) := fit2.2.1
      have Ef42 : f42.Mem (G.ars 3 (G.face x)) := fit2.2.2.1
      have Eh45 : h45.Mem (G.ars 4 (G.face x)) := fit2.2.2.2.1
      exact ⟨by rw [G4, (PRange.mem_pr77 _).mp Es4]; exact Eh45,
        fun q5 hq => ⟨Espoke _ Es4, Ehat _ Eh34, Efan _ 2 Ef41, Efan _ 3 Ef42, hq⟩⟩

/-! #### The fifth sector of the converse part -/

/-- `Part.convPart5` produces the sector of the converse part that describes
the far side of the new hub, together with the range of the new hub arity. -/
theorem fitp_convPart5 [Finite D] (hG : G.Pentagonal) (x : D) (h45 : PRange)
    (hh45 : h45.Mem (G.ars 2 (G.face^[2] (G.edge (G.face^[2] x))))) :
    ∀ p3 : Part, G.Fitp (G.face^[2] x) p3 →
      (Part.convPart5 h45 p3).1.Mem (G.arity (G.edge (G.face^[2] x))) ∧
        G.Fitp (G.face^[2] (G.edge (G.face^[2] x))) (Part.convPart5 h45 p3).2 := by
  have hp59 : ∀ y : D, PRange.pr59.Mem (G.arity y) := fun y => (PRange.mem_pr59 _).mpr (hG y)
  intro p3 hfit
  cases p3 with
  | nil => exact ⟨hp59 _, trivial⟩
  | cons6 h f1 p => exact ⟨hp59 _, trivial⟩
  | cons8 h f1 f2 f3 p => exact ⟨hp59 _, trivial⟩
  | cons u s5 p => exact ⟨hfit.1, hfit.2.1, hh45, trivial⟩
  | cons7 s5 s6 s7 p =>
    exact ⟨hfit.1, hfit.2.1, hh45, hfit.2.2.1, hp59 _, hfit.2.2.2.1, hp59 _, trivial⟩

/-! #### The first two sectors of the converse part -/

/-- `Part.convPart12` produces the two subparts of the converse part that
describe the hat and the spoke that follow the new hub, together with the range
of the hat that follows them. -/
theorem fitp_convPart12 [Finite D] (hp : G.Plain) (hc : G.Cubic) (hG : G.Pentagonal)
    (x : D) : ∀ p4 : Part, G.Fitp (G.face^[3] x) p4 →
    (Part.convPart12 p4).1.Mem (G.ars 2 (G.edge (G.face^[2] x))) ∧
      ∀ q3 : Part, G.Fitp (G.edge (G.face^[2] x)) q3 →
        G.Fitp (G.invFace2 (G.edge (G.face^[2] x))) ((Part.convPart12 p4).2 q3) := by
  have hp59 : ∀ y : D, PRange.pr59.Mem (G.arity y) := fun y => (PRange.mem_pr59 _).mpr (hG y)
  have hm2 : 2 ≤ G.arity (G.edge (G.face^[2] x)) := le_trans (by norm_num) (hG _)
  -- the new hub's hat, that is the spoke of the fourth subpart
  have E0 : G.ars 2 (G.edge (G.face^[2] x)) = G.arity (G.edge (G.face^[4] x)) := by
    change G.arity (G.edge (G.face^[2] (G.edge (G.edge (G.face^[2] x))))) = _
    rw [hp.edge_edge]
    rfl
  -- the spoke of the first subpart is the hat of the fourth spoke of the hub
  have D1 : G.arity (G.edge (G.invFace2 (G.edge (G.face^[2] x))))
      = G.ars 2 (G.face^[3] x) := by
    rw [invFace2_eq_iterate G _ hm2]
    exact (arity_hat_prev G hp hc (G.face^[2] x) rfl hm2).symm
  -- the spoke of the second subpart is the fourth spoke of the hub
  have D2 : G.edge (G.face (G.invFace2 (G.edge (G.face^[2] x))))
      = G.face (G.edge (G.face^[3] x)) := by
    have h1 : G.face (G.invFace2 (G.edge (G.face^[2] x)))
        = G.edge (G.node (G.edge (G.face^[2] x))) := by
      simp only [invFace2]; rw [G.nodeK]
    rw [h1, hp.edge_edge]
    exact (face_edge_face G hp hc (G.face^[2] x)).symm
  have E4 : G.face (G.face (G.invFace2 (G.edge (G.face^[2] x)))) = G.edge (G.face^[2] x) := by
    simp only [invFace2]; rw [G.nodeK, G.nodeK]
  have E1 : ∀ r : PRange, r.Mem (G.ars 2 (G.face^[3] x)) →
      r.Mem (G.arity (G.edge (G.invFace2 (G.edge (G.face^[2] x))))) := by
    intro r h; rw [D1]; exact h
  have E2 : ∀ r : PRange, r.Mem (G.arity (G.edge (G.face^[3] x))) →
      r.Mem (G.arity (G.edge (G.face (G.invFace2 (G.edge (G.face^[2] x)))))) := by
    intro r h; rw [D2, G.arity_face]; exact h
  have E3 : ∀ (r : PRange) (j : ℕ), r.Mem (G.ars (j + 1) (G.face^[3] x)) →
      r.Mem (G.ars j (G.face (G.invFace2 (G.edge (G.face^[2] x))))) := by
    intro r j h
    change r.Mem (G.arity (G.edge (G.face^[j]
      (G.edge (G.face (G.invFace2 (G.edge (G.face^[2] x))))))))
    rw [D2, ← Function.iterate_succ_apply (G.face : D → D) j (G.edge (G.face^[3] x))]
    exact h
  -- the hat of the fifth spoke of the hub, seen from the fourth spoke
  have Dhat : G.ars 2 (G.face^[4] x)
      = G.arity (G.edge (G.face^[G.arity (G.edge (G.face^[3] x)) - 2]
          (G.edge (G.face^[3] x)))) :=
    arity_hat_prev G hp hc (G.face^[3] x) rfl (le_trans (by norm_num) (hG _))
  have Dhat' : ∀ k : ℕ, G.arity (G.edge (G.face^[3] x)) = k + 2 →
      G.arity (G.edge (G.face^[k] (G.edge (G.face^[3] x)))) = G.ars 2 (G.face^[4] x) := by
    intro k hk
    rw [Dhat, hk, Nat.add_sub_cancel]
  have Efanhat : ∀ (r : PRange) (k : ℕ), G.arity (G.edge (G.face^[3] x)) = k + 2 →
      r.Mem (G.ars 2 (G.face^[4] x)) →
      r.Mem (G.arity (G.edge (G.face^[k] (G.edge (G.face^[3] x))))) := by
    intro r k hk h
    rw [Dhat' k hk]; exact h
  have E4' : ∀ q3 : Part, G.Fitp (G.edge (G.face^[2] x)) q3 →
      G.Fitp (G.face (G.face (G.invFace2 (G.edge (G.face^[2] x))))) q3 := by
    intro q3 h; rw [E4]; exact h
  have hdef : PRange.pr59.Mem (G.ars 2 (G.edge (G.face^[2] x))) ∧
      ∀ q3 : Part, G.Fitp (G.edge (G.face^[2] x)) q3 →
        G.Fitp (G.invFace2 (G.edge (G.face^[2] x))) .nil := ⟨hp59 _, fun _ _ => trivial⟩
  intro p4 hfit
  cases p4 with
  | nil => exact hdef
  | cons8 h f1 f2 f3 p => exact hdef
  | cons s2 s1 rest =>
    have Es2 : s2.Mem (G.arity (G.edge (G.face^[3] x))) := hfit.1
    have Es1 : s1.Mem (G.ars 2 (G.face^[3] x)) := hfit.2.1
    have fitr : G.Fitp (G.face^[4] x) rest := hfit.2.2
    cases rest with
    | nil => exact hdef
    | cons6 h f1 p => exact hdef
    | cons7 h f1 f2 p => exact hdef
    | cons8 h f1 f2 f3 p => exact hdef
    | cons h23 f2 p =>
      have Eh23 : h23.Mem (G.arity (G.edge (G.face^[4] x))) := fitr.1
      have Ef2 : f2.Mem (G.ars 2 (G.face^[4] x)) := fitr.2.1
      cases f2 <;> cases s2 <;>
        first
          | exact ⟨by rw [E0]; exact Eh23,
              fun q3 hq => ⟨E1 _ Es1, hp59 _, E2 _ Es2, hp59 _, E4' _ hq⟩⟩
          | exact ⟨by rw [E0]; exact Eh23,
              fun q3 hq => ⟨E1 _ Es1, hp59 _, E2 _ Es2,
                E3 _ 2 (Efanhat _ 3 ((PRange.mem_pr55 _).mp Es2) Ef2), E4' _ hq⟩⟩
          | exact ⟨by rw [E0]; exact Eh23,
              fun q3 hq => ⟨E1 _ Es1, hp59 _, E2 _ Es2, hp59 _,
                E3 _ 3 (Efanhat _ 4 ((PRange.mem_pr66 _).mp Es2) Ef2), E4' _ hq⟩⟩
          | exact ⟨by rw [E0]; exact Eh23,
              fun q3 hq => ⟨E1 _ Es1, hp59 _, E2 _ Es2, hp59 _, hp59 _,
                E3 _ 4 (Efanhat _ 5 ((PRange.mem_pr77 _).mp Es2) Ef2), E4' _ hq⟩⟩
          | exact hdef
  | cons6 s1 h12 rest =>
    have Es2 : PRange.pr66.Mem (G.arity (G.edge (G.face^[3] x))) := hfit.1
    have Es1 : s1.Mem (G.ars 2 (G.face^[3] x)) := hfit.2.1
    have Eh12 : h12.Mem (G.ars 3 (G.face^[3] x)) := hfit.2.2.1
    have fitr : G.Fitp (G.face^[4] x) rest := hfit.2.2.2
    cases rest with
    | nil => exact hdef
    | cons6 h f1 p => exact hdef
    | cons7 h f1 f2 p => exact hdef
    | cons8 h f1 f2 f3 p => exact hdef
    | cons h23 f21 p =>
      have Eh23 : h23.Mem (G.arity (G.edge (G.face^[4] x))) := fitr.1
      have Ef21 : f21.Mem (G.ars 2 (G.face^[4] x)) := fitr.2.1
      exact ⟨by rw [E0]; exact Eh23,
        fun q3 hq => ⟨E1 _ Es1, hp59 _, E2 _ Es2, E3 _ 2 Eh12,
          E3 _ 3 (Efanhat _ 4 ((PRange.mem_pr66 _).mp Es2) Ef21), E4' _ hq⟩⟩
  | cons7 s1 h12 f21 rest =>
    have Es2 : PRange.pr77.Mem (G.arity (G.edge (G.face^[3] x))) := hfit.1
    have Es1 : s1.Mem (G.ars 2 (G.face^[3] x)) := hfit.2.1
    have Eh12 : h12.Mem (G.ars 3 (G.face^[3] x)) := hfit.2.2.1
    have Ef21 : f21.Mem (G.ars 4 (G.face^[3] x)) := hfit.2.2.2.1
    have fitr : G.Fitp (G.face^[4] x) rest := hfit.2.2.2.2
    cases rest with
    | nil => exact hdef
    | cons6 h f1 p => exact hdef
    | cons7 h f1 f2 p => exact hdef
    | cons8 h f1 f2 f3 p => exact hdef
    | cons h23 f22 p =>
      have Eh23 : h23.Mem (G.arity (G.edge (G.face^[4] x))) := fitr.1
      have Ef22 : f22.Mem (G.ars 2 (G.face^[4] x)) := fitr.2.1
      exact ⟨by rw [E0]; exact Eh23,
        fun q3 hq => ⟨E1 _ Es1, hp59 _, E2 _ Es2, E3 _ 2 Eh12, E3 _ 3 Ef21,
          E3 _ 4 (Efanhat _ 5 ((PRange.mem_pr77 _).mp Es2) Ef22), E4' _ hq⟩⟩

/-! #### The third sector of the converse part -/

/-- `Part.convPart3` produces the subpart of the converse part that describes
the hub of `p`. -/
theorem fitp_convPart3 [Finite D] (hp : G.Plain) (x : D) (h23 : PRange) (q : Part)
    (hq : G.Fitp (G.face (G.edge (G.face^[2] x))) q)
    (hh23 : h23.Mem (G.ars 2 (G.edge (G.face^[2] x)))) :
    ∀ p6 : Part, G.arity x = 5 + p6.size → G.Fitp (G.face^[5] x) p6 →
      G.Fitp (G.edge (G.face^[2] x)) (Part.convPart3 h23 p6 q) := by
  have C1 : G.arity (G.edge (G.edge (G.face^[2] x))) = G.arity x := by
    rw [hp.edge_edge, G.arity_iterate_face]
  have C2 : ∀ j : ℕ, G.ars j (G.edge (G.face^[2] x)) = G.arity (G.edge (G.face^[j + 2] x)) := by
    intro j
    change G.arity (G.edge (G.face^[j] (G.edge (G.edge (G.face^[2] x))))) = _
    rw [hp.edge_edge, ← Function.iterate_add_apply]
  have Chub : ∀ (r : PRange) (k : ℕ), G.arity x = k → r.Mem k →
      r.Mem (G.arity (G.edge (G.edge (G.face^[2] x)))) := by
    intro r k hk h; rw [C1, hk]; exact h
  have Cfan : ∀ (r : PRange) (j : ℕ), r.Mem (G.arity (G.edge (G.face^[j + 2] x))) →
      r.Mem (G.ars j (G.edge (G.face^[2] x))) := by
    intro r j h; rw [C2]; exact h
  intro p6 hsize hfit6
  cases p6 with
  | nil => exact ⟨Chub _ 5 hsize (by decide), hh23, hq⟩
  | cons6 h f1 p => exact trivial
  | cons7 h f1 f2 p => exact trivial
  | cons8 h f1 f2 f3 p => exact trivial
  | cons f31 hh31 p7 =>
    have Ef31 : f31.Mem (G.arity (G.edge (G.face^[5] x))) := hfit6.1
    have fit7 : G.Fitp (G.face^[6] x) p7 := hfit6.2.2
    cases p7 with
    | nil => exact ⟨Chub _ 6 hsize (by decide), hh23, hq⟩
    | cons6 h f1 p => exact trivial
    | cons7 h f1 f2 p => exact trivial
    | cons8 h f1 f2 f3 p => exact trivial
    | cons f32 hh32 p8 =>
      have Ef32 : f32.Mem (G.arity (G.edge (G.face^[6] x))) := fit7.1
      have fit8 : G.Fitp (G.face^[7] x) p8 := fit7.2.2
      cases p8 with
      | nil =>
        cases f31 <;> cases f32 <;>
          first
            | exact ⟨Chub _ 7 hsize (by decide), hh23, hq⟩
            | exact ⟨Chub _ 7 hsize (by decide), hh23, Cfan _ 3 Ef31, Cfan _ 4 Ef32, hq⟩
      | cons6 h f1 p => exact trivial
      | cons7 h f1 f2 p => exact trivial
      | cons8 h f1 f2 f3 p => exact trivial
      | cons f33 hh33 p9 =>
        have Ef33 : f33.Mem (G.arity (G.edge (G.face^[7] x))) := fit8.1
        cases p9 with
        | nil =>
          exact ⟨Chub _ 8 hsize (by decide), hh23, Cfan _ 3 Ef31, Cfan _ 4 Ef32,
            Cfan _ 5 Ef33, hq⟩
        | cons s h p => exact trivial
        | cons6 h f1 p => exact trivial
        | cons7 h f1 f2 p => exact trivial
        | cons8 h f1 f2 f3 p => exact trivial

/-! #### The converse fitting theorem -/

/-- Mirroring twice backwards does not change the arity. -/
theorem arity_invFace2 [Finite D] (y : D) : G.arity (G.invFace2 y) = G.arity y := by
  simp only [invFace2]; rw [arity_edge_node, arity_edge_node]

/-- The converse of a part fits the dart two face steps back from the third
spoke of the hub. -/
theorem fitp_converse [Finite D] (hp : G.Plain) (hc : G.Cubic) (hG : G.Pentagonal)
    (p1 : Part) (x : D) (hfit : G.ExactFitp x p1) :
    G.TightFitp (G.invFace2 (G.edge (G.face^[2] x))) (Part.conversePart p1).1
      (Part.conversePart p1).2 := by
  obtain ⟨hsz, hf⟩ := hfit
  obtain ⟨Eh45, fit_q4⟩ := fitp_convPart4 G hp hc hG x p1 hf
  obtain ⟨Eu, fit_q5⟩ :=
    fitp_convPart5 G hG x (Part.convPart4 p1).1 Eh45 (p1.drop 2) (G.fitp_drop 2 hf)
  obtain ⟨Eh23, fit_q12⟩ := fitp_convPart12 G hp hc hG x (p1.drop 3) (G.fitp_drop 3 hf)
  have hsize : G.arity x = 5 + (p1.drop 5).size := by
    have h5 : 5 ≤ p1.size := by have := hG x; omega
    rw [Part.size_drop]; omega
  have fit3 := fitp_convPart3 G hp x (Part.convPart12 (p1.drop 3)).1
    ((Part.convPart4 p1).2 (Part.convPart5 (Part.convPart4 p1).1 (p1.drop 2)).2)
    (fit_q4 _ fit_q5) Eh23 (p1.drop 5) hsize (G.fitp_drop 5 hf)
  exact ⟨by rw [arity_invFace2]; exact Eu, fit_q12 _ fit3⟩

end Hypermap

end FourColor

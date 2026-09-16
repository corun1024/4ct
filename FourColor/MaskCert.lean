import FourColor.Chromogram

/-!
# Certified traces as colour masks

The coverage check walks the chromogram tree once per configuration, carrying a
bitmask over certified traces — "which traces still match this chromogram
prefix".  Descending by a symbol intersects that mask with a fixed
`colour at this position` mask, so a node costs a couple of `Nat` primitives
however many traces there are.

For that to mean anything the masks have to correspond to the traces.  Rather
than store the traces and *prove* the correspondence — which would cost as much
as the walk it is meant to justify — the masks are taken as the definition: bit
`i` of `colourMask p c` says that trace `i` has colour `c` at position `p`.  All
that must then be checked is that the masks are *consistent*, i.e. that at each
position the three colours partition the traces, and that is a handful of `Nat`
operations per position.

`Masks.traceOf` reads a trace back out, and `getD_traceOf` is the bridge the
walk's soundness proof needs: the colour of trace `i` at position `p` is `c`
exactly when bit `i` of `colourMask p c` is set.
-/

namespace FourColor

/-- The colour masks of a certificate: `colourMask p c` has bit `i` set when the
`i`-th certified trace has colour `c` at position `p`.  `width` is the number of
traces and `len` the ring size. -/
structure Masks where
  /-- Ring size: the length of every certified trace. -/
  len : ℕ
  /-- How many traces the masks describe. -/
  width : ℕ
  /-- `colourMask p c`, for `c` among `c1`, `c2`, `c3`. -/
  colourMask : ℕ → Color → ℕ

namespace Masks

/-- All trace indices below `width`. -/
def full (ms : Masks) : ℕ := 2 ^ ms.width - 1

/-- At position `p` the three colours partition the traces: every trace has one,
and no trace has two. -/
def consistentAt (ms : Masks) (p : ℕ) : Prop :=
  (∀ i < ms.width, ∃ c, (c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3) ∧
      (ms.colourMask p c).testBit i) ∧
  (∀ i, ∀ c c', (ms.colourMask p c).testBit i → (ms.colourMask p c').testBit i →
      (c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3) →
      (c' = Color.c1 ∨ c' = Color.c2 ∨ c' = Color.c3) → c = c')

/-- The masks are consistent at every position of the ring. -/
def Consistent (ms : Masks) : Prop := ∀ p < ms.len, ms.consistentAt p

/-- The colour of trace `i` at position `p`, read out of the masks.  `c0` stands
for "no colour", which consistency rules out below `width`. -/
noncomputable def colourAt (ms : Masks) (p i : ℕ) : Color :=
  if (ms.colourMask p Color.c1).testBit i then Color.c1
  else if (ms.colourMask p Color.c2).testBit i then Color.c2
  else if (ms.colourMask p Color.c3).testBit i then Color.c3
  else Color.c0

/-- Trace `i`, read out of the masks position by position. -/
noncomputable def traceOf (ms : Masks) (i : ℕ) : List Color :=
  (List.range ms.len).map (fun p => ms.colourAt p i)

@[simp] theorem length_traceOf (ms : Masks) (i : ℕ) :
    (ms.traceOf i).length = ms.len := by
  simp [traceOf]

/-- Reading position `p` of trace `i` gives what the masks say. -/
theorem getElem_traceOf (ms : Masks) (i p : ℕ) (hp : p < ms.len) :
    (ms.traceOf i)[p]'(by simpa using hp) = ms.colourAt p i := by
  simp [traceOf, List.getElem_map, List.getElem_range]

/-- **The bridge.**  Under consistency, trace `i` has colour `c` at position `p`
exactly when bit `i` of `colourMask p c` is set. -/
theorem colourAt_eq_iff (ms : Masks) {p i : ℕ} (hp : p < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent) {c : Color}
    (hc3 : c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3) :
    ms.colourAt p i = c ↔ (ms.colourMask p c).testBit i := by
  obtain ⟨hexists, hunique⟩ := hc p hp
  constructor
  · intro h
    -- `colourAt` picked `c`, so the corresponding bit was the first one set
    unfold colourAt at h
    split at h
    · subst h; assumption
    · split at h
      · subst h; assumption
      · split at h
        · subst h; assumption
        · -- no bit set, contradicting existence
          obtain ⟨c', hc', hbit⟩ := hexists i hi
          rcases hc' with rfl | rfl | rfl <;> simp_all
  · intro hbit
    -- some colour is chosen; uniqueness forces it to be `c`
    unfold colourAt
    split
    · next h1 => exact hunique i _ _ h1 hbit (Or.inl rfl) hc3
    · split
      · next _ h2 => exact hunique i _ _ h2 hbit (Or.inr (Or.inl rfl)) hc3
      · split
        · next _ _ h3 => exact hunique i _ _ h3 hbit (Or.inr (Or.inr rfl)) hc3
        · next h1 h2 h3 =>
          exfalso
          rcases hc3 with rfl | rfl | rfl <;> simp_all

/-! ### The descent masks

Each chromogram symbol restricts which traces can still match.  `skip` demands
`c1` here; `push` demands `c2` or `c3`; a pop demands a colour here that agrees
(`pop0`) or disagrees (`pop1`) with the colour pushed at the matching position.
Each is one fixed `Nat` per position (or pair of positions), so a descent is an
intersection. -/

/-- `skip`: this position must be `c1`. -/
def skipMask (ms : Masks) (p : ℕ) : ℕ := ms.colourMask p Color.c1

/-- `push`: this position must be `c2` or `c3`. -/
def pushMask (ms : Masks) (p : ℕ) : ℕ :=
  ms.colourMask p Color.c2 ||| ms.colourMask p Color.c3

/-- `pop0`: this position agrees with the colour pushed at `q`. -/
def pop0Mask (ms : Masks) (p q : ℕ) : ℕ :=
  (ms.colourMask p Color.c2 &&& ms.colourMask q Color.c2) |||
  (ms.colourMask p Color.c3 &&& ms.colourMask q Color.c3)

/-- `pop1`: this position disagrees with the colour pushed at `q`. -/
def pop1Mask (ms : Masks) (p q : ℕ) : ℕ :=
  (ms.colourMask p Color.c2 &&& ms.colourMask q Color.c3) |||
  (ms.colourMask p Color.c3 &&& ms.colourMask q Color.c2)

/-- `colourAt_eq_iff` as a `Bool` equation, so the descent masks can be rewritten
one colour at a time. -/
theorem testBit_colourMask (ms : Masks) {p i : ℕ} (hp : p < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent) (c : Color)
    (hc3 : c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3) :
    (ms.colourMask p c).testBit i = decide (ms.colourAt p i = c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact (ms.colourAt_eq_iff hp hi hc hc3).symm

/-- Below `width`, consistency gives every trace a real colour at every
position, so `c0` -- the "no colour" case of `colourAt` -- never occurs. -/
theorem colourAt_ne_c0 (ms : Masks) {p i : ℕ} (hp : p < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent) : ms.colourAt p i ≠ Color.c0 := by
  obtain ⟨hex, -⟩ := hc p hp
  obtain ⟨c, hc3, hbit⟩ := hex i hi
  rw [(ms.colourAt_eq_iff hp hi hc hc3).mpr hbit]
  rcases hc3 with rfl | rfl | rfl <;> simp

theorem testBit_skipMask (ms : Masks) {p i : ℕ} (hp : p < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent) :
    (ms.skipMask p).testBit i ↔ ms.colourAt p i = Color.c1 :=
  (ms.colourAt_eq_iff hp hi hc (Or.inl rfl)).symm

theorem testBit_pushMask (ms : Masks) {p i : ℕ} (hp : p < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent) :
    (ms.pushMask p).testBit i ↔
      (ms.colourAt p i = Color.c2 ∨ ms.colourAt p i = Color.c3) := by
  rw [pushMask, Nat.testBit_or,
    ms.testBit_colourMask hp hi hc Color.c2 (Or.inr (Or.inl rfl)),
    ms.testBit_colourMask hp hi hc Color.c3 (Or.inr (Or.inr rfl))]
  simp

theorem testBit_pop0Mask (ms : Masks) {p q i : ℕ} (hp : p < ms.len) (hq : q < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent) :
    (ms.pop0Mask p q).testBit i ↔
      ((ms.colourAt p i = Color.c2 ∧ ms.colourAt q i = Color.c2) ∨
       (ms.colourAt p i = Color.c3 ∧ ms.colourAt q i = Color.c3)) := by
  rw [pop0Mask, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and,
    ms.testBit_colourMask hp hi hc Color.c2 (Or.inr (Or.inl rfl)),
    ms.testBit_colourMask hq hi hc Color.c2 (Or.inr (Or.inl rfl)),
    ms.testBit_colourMask hp hi hc Color.c3 (Or.inr (Or.inr rfl)),
    ms.testBit_colourMask hq hi hc Color.c3 (Or.inr (Or.inr rfl))]
  simp

theorem testBit_pop1Mask (ms : Masks) {p q i : ℕ} (hp : p < ms.len) (hq : q < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent) :
    (ms.pop1Mask p q).testBit i ↔
      ((ms.colourAt p i = Color.c2 ∧ ms.colourAt q i = Color.c3) ∨
       (ms.colourAt p i = Color.c3 ∧ ms.colourAt q i = Color.c2)) := by
  rw [pop1Mask, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and,
    ms.testBit_colourMask hp hi hc Color.c2 (Or.inr (Or.inl rfl)),
    ms.testBit_colourMask hq hi hc Color.c3 (Or.inr (Or.inr rfl)),
    ms.testBit_colourMask hp hi hc Color.c3 (Or.inr (Or.inr rfl)),
    ms.testBit_colourMask hq hi hc Color.c2 (Or.inr (Or.inl rfl))]
  simp

/-- The bit a chord carries: whether the edge starting it was `c3`.  Written as
a match rather than `== Color.c3` so that it reduces definitionally once the
colour is known, which is what the step lemmas below rely on. -/
def chordBit : Color → Bool
  | Color.c3 => true
  | _        => false

/-- The chord stack `matchg` would be carrying for trace `i`, recovered from the
walk's stack of chord *positions*: a chord pushed at `q` carries the bit saying
its colour there was `c3`. -/
noncomputable def bsOf (ms : Masks) (i : ℕ) (stack : List ℕ) : List Bool :=
  stack.map (fun q => chordBit (ms.colourAt q i))

@[simp] theorem bsOf_nil (ms : Masks) (i : ℕ) : ms.bsOf i [] = [] := rfl

@[simp] theorem bsOf_cons (ms : Masks) (i q : ℕ) (stack : List ℕ) :
    ms.bsOf i (q :: stack) = chordBit (ms.colourAt q i) :: ms.bsOf i stack := rfl

/-! ### The descent masks are exactly `matchStep`

Each lemma says: trace `i` survives this descent precisely when `matchStep`
accepts its colour here against the symbol, and that the walk's new position
stack denotes the chord stack `matchg` would carry next.  These are what let a
mask walk stand in for a per-trace `matchg`. -/

theorem skipMask_iff (ms : Masks) {p i : ℕ} (hp : p < ms.len) (hi : i < ms.width)
    (hc : ms.Consistent) (stack : List ℕ) :
    (ms.skipMask p).testBit i ↔
      matchStep (ms.colourAt p i) GramSymbol.skip (ms.bsOf i stack)
        = some (ms.bsOf i stack) := by
  rw [ms.testBit_skipMask hp hi hc]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    cases hcol : ms.colourAt p i with
    | c1 => rfl
    | c0 => rw [hcol] at h; simp [matchStep, chordBit] at h
    | c2 => rw [hcol] at h; simp [matchStep, chordBit] at h
    | c3 => rw [hcol] at h; simp [matchStep, chordBit] at h

theorem pushMask_iff (ms : Masks) {p i : ℕ} (hp : p < ms.len) (hi : i < ms.width)
    (hc : ms.Consistent) (stack : List ℕ) :
    (ms.pushMask p).testBit i ↔
      matchStep (ms.colourAt p i) GramSymbol.push (ms.bsOf i stack)
        = some (ms.bsOf i (p :: stack)) := by
  rw [ms.testBit_pushMask hp hi hc, bsOf_cons]
  constructor
  · rintro (h | h) <;> rw [h] <;> simp [matchStep, chordBit]
  · intro h
    cases hcol : ms.colourAt p i with
    | c2 => exact Or.inl rfl
    | c3 => exact Or.inr rfl
    | c0 => rw [hcol] at h; simp [matchStep, chordBit] at h
    | c1 => rw [hcol] at h; simp [matchStep, chordBit] at h

theorem pop0Mask_iff (ms : Masks) {p q i : ℕ} (hp : p < ms.len) (hq : q < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent)
    (hq23 : ms.colourAt q i = Color.c2 ∨ ms.colourAt q i = Color.c3)
    (stack : List ℕ) :
    (ms.pop0Mask p q).testBit i ↔
      matchStep (ms.colourAt p i) GramSymbol.pop0 (ms.bsOf i (q :: stack))
        = some (ms.bsOf i stack) := by
  rw [ms.testBit_pop0Mask hp hq hi hc, bsOf_cons]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rw [h1, h2] <;> simp [matchStep, chordBit]
  · intro h
    rcases hq23 with hqc | hqc <;>
      cases hcp : ms.colourAt p i <;>
      rw [hcp, hqc] at h <;> simp_all [matchStep, chordBit]

theorem pop1Mask_iff (ms : Masks) {p q i : ℕ} (hp : p < ms.len) (hq : q < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent)
    (hq23 : ms.colourAt q i = Color.c2 ∨ ms.colourAt q i = Color.c3)
    (stack : List ℕ) :
    (ms.pop1Mask p q).testBit i ↔
      matchStep (ms.colourAt p i) GramSymbol.pop1 (ms.bsOf i (q :: stack))
        = some (ms.bsOf i stack) := by
  rw [ms.testBit_pop1Mask hp hq hi hc, bsOf_cons]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rw [h1, h2] <;> simp [matchStep, chordBit]
  · intro h
    rcases hq23 with hqc | hqc <;>
      cases hcp : ms.colourAt p i <;>
      rw [hcp, hqc] at h <;> simp_all [matchStep, chordBit]

/-! ### The walk

`walk` descends the chromogram tree once, carrying the set of traces that still
match the prefix.  `leafOk` is asked about each chord context the walk bottoms
out in; the certificate supplies it, and it is opaque here.

The walk is written over the list of remaining positions so the recursion is
structural, which is also the shape the generator emits. -/

/-- Every chromogram matching the rest of trace `i` from the given position list
bottoms out somewhere `leafOk` accepts.  This is what the walk decides. -/
def Covers (ms : Masks) (leafOk : List ℕ → ℕ → Bool) :
    List ℕ → List ℕ → ℕ → Prop
  | [],     stack, a => ∀ i, a.testBit i → stack = [] → leafOk stack a = true
  | p :: ps, stack, a =>
      (Covers ms leafOk ps stack (a &&& ms.skipMask p)) ∧
      (Covers ms leafOk ps (p :: stack) (a &&& ms.pushMask p)) ∧
      (match stack with
       | [] => True
       | q :: rest =>
           Covers ms leafOk ps rest (a &&& ms.pop0Mask p q) ∧
           Covers ms leafOk ps rest (a &&& ms.pop1Mask p q))

theorem covers_nil (ms : Masks) (leafOk : List ℕ → ℕ → Bool) (stack : List ℕ) (a : ℕ) :
    ms.Covers leafOk [] stack a ↔
      ∀ i, a.testBit i = true → stack = [] → leafOk stack a = true :=
  Iff.rfl

theorem covers_cons (ms : Masks) (leafOk : List ℕ → ℕ → Bool)
    (p : ℕ) (ps stack : List ℕ) (a : ℕ) :
    ms.Covers leafOk (p :: ps) stack a ↔
      ((ms.Covers leafOk ps stack (a &&& ms.skipMask p)) ∧
       (ms.Covers leafOk ps (p :: stack) (a &&& ms.pushMask p)) ∧
       (match stack with
        | [] => True
        | q :: rest =>
            ms.Covers leafOk ps rest (a &&& ms.pop0Mask p q) ∧
            ms.Covers leafOk ps rest (a &&& ms.pop1Mask p q))) :=
  Iff.rfl

/-- The walk itself: the decidable counterpart of `Covers`.  An empty mask means
no certified trace reaches this subtree, so it is vacuously covered — that test
is what prunes, and the caller does not repeat it. -/
def walk (ms : Masks) (leafOk : List ℕ → ℕ → Bool) :
    List ℕ → List ℕ → ℕ → Bool
  | [],      stack, a => !stack.isEmpty || leafOk stack a
  | p :: ps, stack, a =>
      if a == 0 then true else
        walk ms leafOk ps stack (a &&& ms.skipMask p) &&
        walk ms leafOk ps (p :: stack) (a &&& ms.pushMask p) &&
        (match stack with
         | [] => true
         | q :: rest =>
             walk ms leafOk ps rest (a &&& ms.pop0Mask p q) &&
             walk ms leafOk ps rest (a &&& ms.pop1Mask p q))

/-- The same walk with the remaining positions counted off by a fuel and a
starting position.  That is the shape a generated module emits, because the
kernel evaluates a `Nat` successor more cheaply than it destructures a list. -/
def walkFuel (ms : Masks) (leafOk : List ℕ → ℕ → Bool) :
    ℕ → ℕ → List ℕ → ℕ → Bool
  | 0,        _, stack, a => !stack.isEmpty || leafOk stack a
  | fuel + 1, p, stack, a =>
      if a == 0 then true else
        ms.walkFuel leafOk fuel (p + 1) stack (a &&& ms.skipMask p) &&
        ms.walkFuel leafOk fuel (p + 1) (p :: stack) (a &&& ms.pushMask p) &&
        (match stack with
         | [] => true
         | q :: rest =>
             ms.walkFuel leafOk fuel (p + 1) rest (a &&& ms.pop0Mask p q) &&
             ms.walkFuel leafOk fuel (p + 1) rest (a &&& ms.pop1Mask p q))

/-- The two shapes agree. -/
theorem walkFuel_eq (ms : Masks) (leafOk : List ℕ → ℕ → Bool) :
    ∀ (fuel p : ℕ) (stack : List ℕ) (a : ℕ),
      ms.walkFuel leafOk fuel p stack a = ms.walk leafOk (List.range' p fuel) stack a := by
  intro fuel
  induction fuel with
  | zero => intro p stack a; rfl
  | succ fuel ih =>
    intro p stack a
    rw [List.range'_succ]
    simp only [walkFuel, walk, ih]

/-- A zero mask has no bits, so nothing is required of it. -/
theorem covers_of_zero (ms : Masks) (leafOk : List ℕ → ℕ → Bool)
    (ps : List ℕ) (stack : List ℕ) : ms.Covers leafOk ps stack 0 := by
  induction ps generalizing stack with
  | nil => intro i hi; simp at hi
  | cons p ps ih =>
    refine ⟨?_, ?_, ?_⟩
    · simpa using ih stack
    · simpa using ih (p :: stack)
    · cases stack with
      | nil => trivial
      | cons q rest => exact ⟨by simpa using ih rest, by simpa using ih rest⟩

/-- **The walk decides `Covers`.**  Everything the walk accepts really is
covered; this is the half the certificate needs. -/
theorem covers_of_walk (ms : Masks) (leafOk : List ℕ → ℕ → Bool) :
    ∀ (ps stack : List ℕ) (a : ℕ),
      ms.walk leafOk ps stack a = true → ms.Covers leafOk ps stack a := by
  intro ps
  induction ps with
  | nil =>
    intro stack a h i hi hst
    subst hst
    simp only [walk, List.isEmpty_nil, Bool.not_true, Bool.false_or] at h
    exact h
  | cons p ps ih =>
    intro stack a h
    by_cases hz : a = 0
    · subst hz; exact ms.covers_of_zero leafOk (p :: ps) stack
    · have hzb : (a == 0) = false := by simpa using hz
      simp only [walk, hzb, Bool.false_eq_true, ite_false,
        Bool.and_eq_true_iff] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨ih _ _ h1, ih _ _ h2, ?_⟩
      cases stack with
      | nil => trivial
      | cons q rest =>
        simp only [Bool.and_eq_true_iff] at h3
        exact ⟨ih _ _ h3.1, ih _ _ h3.2⟩

/-! ### One step of the walk against one step of `matchg`

Four small lemmas, one per symbol: if `matchStep` accepts trace `i`'s colour
here, then the walk's descent mask keeps `i`, and the chord context `matchStep`
returns is the one the walk's new position stack denotes. -/

/-- Every position on the chord stack was pushed, so it carries a chord colour. -/
def StackOk (ms : Masks) (i : ℕ) (stack : List ℕ) : Prop :=
  ∀ q ∈ stack, q < ms.len ∧
    (ms.colourAt q i = Color.c2 ∨ ms.colourAt q i = Color.c3)

theorem step_skip (ms : Masks) {p i : ℕ} (hp : p < ms.len) (hi : i < ms.width)
    (hc : ms.Consistent) (stack : List ℕ) {lb' : List Bool}
    (h : matchStep (ms.colourAt p i) GramSymbol.skip (ms.bsOf i stack) = some lb') :
    lb' = ms.bsOf i stack ∧ (ms.skipMask p).testBit i := by
  cases hcol : ms.colourAt p i <;> rw [hcol] at h <;> simp [matchStep, chordBit] at h
  subst h
  exact ⟨rfl, (ms.skipMask_iff hp hi hc stack).mpr (by rw [hcol]; rfl)⟩

theorem step_push (ms : Masks) {p i : ℕ} (hp : p < ms.len) (hi : i < ms.width)
    (hc : ms.Consistent) (stack : List ℕ) {lb' : List Bool}
    (h : matchStep (ms.colourAt p i) GramSymbol.push (ms.bsOf i stack) = some lb') :
    lb' = ms.bsOf i (p :: stack) ∧ (ms.pushMask p).testBit i ∧
      (ms.colourAt p i = Color.c2 ∨ ms.colourAt p i = Color.c3) := by
  cases hcol : ms.colourAt p i with
  | c0 => rw [hcol] at h; simp [matchStep, chordBit] at h
  | c1 => rw [hcol] at h; simp [matchStep, chordBit] at h
  | c2 =>
    have h23 : ms.colourAt p i = Color.c2 ∨ ms.colourAt p i = Color.c3 := Or.inl hcol
    rw [hcol] at h; simp [matchStep, chordBit] at h
    refine ⟨?_, (ms.testBit_pushMask hp hi hc).mpr h23, Or.inl rfl⟩
    rw [bsOf_cons, hcol, ← h]; rfl
  | c3 =>
    have h23 : ms.colourAt p i = Color.c2 ∨ ms.colourAt p i = Color.c3 := Or.inr hcol
    rw [hcol] at h; simp [matchStep, chordBit] at h
    refine ⟨?_, (ms.testBit_pushMask hp hi hc).mpr h23, Or.inr rfl⟩
    rw [bsOf_cons, hcol, ← h]; rfl

theorem step_pop0 (ms : Masks) {p q i : ℕ} (hp : p < ms.len) (hq : q < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent)
    (hq23 : ms.colourAt q i = Color.c2 ∨ ms.colourAt q i = Color.c3)
    (rest : List ℕ) {lb' : List Bool}
    (h : matchStep (ms.colourAt p i) GramSymbol.pop0 (ms.bsOf i (q :: rest)) = some lb') :
    lb' = ms.bsOf i rest ∧ (ms.pop0Mask p q).testBit i := by
  have hbs : ms.bsOf i (q :: rest)
      = chordBit (ms.colourAt q i) :: ms.bsOf i rest := bsOf_cons ..
  cases hcol : ms.colourAt p i with
  | c0 => rw [hcol, hbs] at h; rcases hq23 with hq' | hq' <;> rw [hq'] at h <;>
          simp [matchStep, chordBit] at h
  | c1 => rw [hcol, hbs] at h; rcases hq23 with hq' | hq' <;> rw [hq'] at h <;>
          simp [matchStep, chordBit] at h
  | c2 =>
    rcases hq23 with hq' | hq'
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h
      exact ⟨h.symm, (ms.testBit_pop0Mask hp hq hi hc).mpr (Or.inl ⟨hcol, hq'⟩)⟩
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h
  | c3 =>
    rcases hq23 with hq' | hq'
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h
      exact ⟨h.symm, (ms.testBit_pop0Mask hp hq hi hc).mpr (Or.inr ⟨hcol, hq'⟩)⟩

theorem step_pop1 (ms : Masks) {p q i : ℕ} (hp : p < ms.len) (hq : q < ms.len)
    (hi : i < ms.width) (hc : ms.Consistent)
    (hq23 : ms.colourAt q i = Color.c2 ∨ ms.colourAt q i = Color.c3)
    (rest : List ℕ) {lb' : List Bool}
    (h : matchStep (ms.colourAt p i) GramSymbol.pop1 (ms.bsOf i (q :: rest)) = some lb') :
    lb' = ms.bsOf i rest ∧ (ms.pop1Mask p q).testBit i := by
  have hbs : ms.bsOf i (q :: rest)
      = chordBit (ms.colourAt q i) :: ms.bsOf i rest := bsOf_cons ..
  cases hcol : ms.colourAt p i with
  | c0 => rw [hcol, hbs] at h; rcases hq23 with hq' | hq' <;> rw [hq'] at h <;>
          simp [matchStep, chordBit] at h
  | c1 => rw [hcol, hbs] at h; rcases hq23 with hq' | hq' <;> rw [hq'] at h <;>
          simp [matchStep, chordBit] at h
  | c2 =>
    rcases hq23 with hq' | hq'
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h
      exact ⟨h.symm, (ms.testBit_pop1Mask hp hq hi hc).mpr (Or.inl ⟨hcol, hq'⟩)⟩
  | c3 =>
    rcases hq23 with hq' | hq'
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h
      exact ⟨h.symm, (ms.testBit_pop1Mask hp hq hi hc).mpr (Or.inr ⟨hcol, hq'⟩)⟩
    · rw [hcol, hbs, hq'] at h; simp [matchStep, chordBit] at h

/-! ### `Covers` really is a statement about `matchg`

The walk descends a chromogram tree, but the certificate needs a statement about
`matchg` on individual traces.  This is the bridge: if a subtree is covered and
trace `i` is still live in it, then following any chromogram `matchg` accepts for
`i` lands on a leaf the certificate's test accepted, with `i` still live there. -/

/-- **`Covers` gives the per-trace `matchg` obligation.** -/
theorem leaf_of_covers (ms : Masks) (hc : ms.Consistent)
    (leafOk : List ℕ → ℕ → Bool) {i : ℕ} (hi : i < ms.width) :
    ∀ (ps stack : List ℕ) (a : ℕ) (w : Chromogram),
      (∀ p ∈ ps, p < ms.len) → ms.StackOk i stack →
      ms.Covers leafOk ps stack a → a.testBit i = true →
      matchg (ms.bsOf i stack) (ps.map (fun p => ms.colourAt p i)) w = true →
      ∃ stack' a', leafOk stack' a' = true ∧ a'.testBit i = true := by
  intro ps
  induction ps with
  | nil =>
    intro stack a w _ _ hcov ha hm
    rw [covers_nil] at hcov
    cases w with
    | nil =>
      -- a finished chromogram leaves no open chord, so the stack is empty
      have hbs : ms.bsOf i stack = [] := by simpa [matchg] using hm
      have hst0 : stack = [] := by
        have hl := congrArg List.length hbs
        simpa [bsOf] using hl
      exact ⟨stack, a, hcov i ha hst0, ha⟩
    | cons s w => simp [matchg] at hm
  | cons p ps ih =>
    intro stack a w hlen hst hcov ha hm
    have hp : p < ms.len := hlen p (List.mem_cons_self)
    have hlen' : ∀ x ∈ ps, x < ms.len := fun x hx => hlen x (List.mem_cons_of_mem _ hx)
    cases w with
    | nil => simp [matchg] at hm
    | cons s w =>
      rw [List.map_cons, matchg_cons] at hm
      rw [covers_cons] at hcov
      obtain ⟨hcs, hcp, hcq⟩ := hcov
      cases s with
      | skip =>
        cases hstep : matchStep (ms.colourAt p i) GramSymbol.skip (ms.bsOf i stack) with
        | none => rw [hstep] at hm; simp at hm
        | some lb' =>
          obtain ⟨heq, hbit⟩ := ms.step_skip hp hi hc stack hstep
          rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
          exact ih _ _ w hlen' hst hcs (by simp [Nat.testBit_and, ha, hbit]) hm
      | push =>
        cases hstep : matchStep (ms.colourAt p i) GramSymbol.push (ms.bsOf i stack) with
        | none => rw [hstep] at hm; simp at hm
        | some lb' =>
          obtain ⟨heq, hbit, h23⟩ := ms.step_push hp hi hc stack hstep
          rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
          refine ih _ _ w hlen' ?_ hcp (by simp [Nat.testBit_and, ha, hbit]) hm
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨hp, h23⟩
          · exact hst x hx'
      | pop0 =>
        cases stack with
        | nil =>
          rw [bsOf_nil] at hm
          cases hcol : ms.colourAt p i <;> rw [hcol] at hm <;> simp [matchStep] at hm
        | cons q rest =>
          obtain ⟨hq, hq23⟩ := hst q (List.mem_cons_self)
          cases hstep : matchStep (ms.colourAt p i) GramSymbol.pop0 (ms.bsOf i (q :: rest)) with
          | none => rw [hstep] at hm; simp at hm
          | some lb' =>
            obtain ⟨heq, hbit⟩ := ms.step_pop0 hp hq hi hc hq23 rest hstep
            rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
            exact ih _ _ w hlen' (fun x hx => hst x (List.mem_cons_of_mem _ hx))
              hcq.1 (by simp [Nat.testBit_and, ha, hbit]) hm
      | pop1 =>
        cases stack with
        | nil =>
          rw [bsOf_nil] at hm
          cases hcol : ms.colourAt p i <;> rw [hcol] at hm <;> simp [matchStep] at hm
        | cons q rest =>
          obtain ⟨hq, hq23⟩ := hst q (List.mem_cons_self)
          cases hstep : matchStep (ms.colourAt p i) GramSymbol.pop1 (ms.bsOf i (q :: rest)) with
          | none => rw [hstep] at hm; simp at hm
          | some lb' =>
            obtain ⟨heq, hbit⟩ := ms.step_pop1 hp hq hi hc hq23 rest hstep
            rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
            exact ih _ _ w hlen' (fun x hx => hst x (List.mem_cons_of_mem _ hx))
              hcq.2 (by simp [Nat.testBit_and, ha, hbit]) hm

/-! ### Descending by a given chromogram

`leaf_of_covers` shows that a live trace *reaches* a leaf.  To hand back a
witness the certificate also needs the other direction: whatever survives at a
leaf really does match the chromogram that led there.  That direction is
available because the `*Mask_iff` lemmas are equivalences, not just
implications. -/

/-- Descend by a whole chromogram, returning the surviving mask.  `none` when the
chromogram does not fit the positions (wrong length, or a pop with no open
chord). -/
def maskAfter (ms : Masks) : List ℕ → List ℕ → Chromogram → ℕ → Option ℕ
  | [],      stack, [],          a => if stack.isEmpty then some a else none
  | p :: ps, stack, .skip :: w,  a => ms.maskAfter ps stack w (a &&& ms.skipMask p)
  | p :: ps, stack, .push :: w,  a => ms.maskAfter ps (p :: stack) w (a &&& ms.pushMask p)
  | p :: ps, stack, .pop0 :: w,  a =>
      match stack with
      | []        => none
      | q :: rest => ms.maskAfter ps rest w (a &&& ms.pop0Mask p q)
  | p :: ps, stack, .pop1 :: w,  a =>
      match stack with
      | []        => none
      | q :: rest => ms.maskAfter ps rest w (a &&& ms.pop1Mask p q)
  | _,       _,     _,           _ => none

/-- Masks only shrink, so a trace alive at a leaf was alive at every ancestor. -/
theorem testBit_of_maskAfter (ms : Masks) {j : ℕ} :
    ∀ (ps stack : List ℕ) (w : Chromogram) (a a' : ℕ),
      ms.maskAfter ps stack w a = some a' → a'.testBit j = true → a.testBit j = true := by
  intro ps
  induction ps with
  | nil =>
    intro stack w a a' hm ha
    cases w with
    | cons s w => simp [maskAfter] at hm
    | nil =>
      rw [maskAfter] at hm
      split at hm
      · cases hm; exact ha
      · simp at hm
  | cons p ps ih =>
    intro stack w a a' hm ha
    cases w with
    | nil => simp [maskAfter] at hm
    | cons s w =>
      cases s with
      | skip =>
        rw [maskAfter] at hm
        have h := ih _ _ _ _ hm ha
        rw [Nat.testBit_and] at h
        exact (Bool.and_eq_true_iff.mp h).1
      | push =>
        rw [maskAfter] at hm
        have h := ih _ _ _ _ hm ha
        rw [Nat.testBit_and] at h
        exact (Bool.and_eq_true_iff.mp h).1
      | pop0 =>
        cases stack with
        | nil => rw [maskAfter] at hm; simp at hm
        | cons q rest =>
          rw [maskAfter] at hm
          have h := ih _ _ _ _ hm ha
          rw [Nat.testBit_and] at h
          exact (Bool.and_eq_true_iff.mp h).1
      | pop1 =>
        cases stack with
        | nil => rw [maskAfter] at hm; simp at hm
        | cons q rest =>
          rw [maskAfter] at hm
          have h := ih _ _ _ _ hm ha
          rw [Nat.testBit_and] at h
          exact (Bool.and_eq_true_iff.mp h).1

/-- **Whatever survives a descent matches the chromogram that drove it.** -/
theorem matchg_of_maskAfter (ms : Masks) (hc : ms.Consistent) {j : ℕ}
    (hj : j < ms.width) :
    ∀ (ps stack : List ℕ) (w : Chromogram) (a a' : ℕ),
      (∀ p ∈ ps, p < ms.len) → ms.StackOk j stack →
      ms.maskAfter ps stack w a = some a' → a'.testBit j = true →
      matchg (ms.bsOf j stack) (ps.map (fun p => ms.colourAt p j)) w = true := by
  intro ps
  induction ps with
  | nil =>
    intro stack w a a' _ _ hm ha
    cases w with
    | cons s w => simp [maskAfter] at hm
    | nil =>
      rw [maskAfter] at hm
      split at hm
      · next hst =>
        rw [List.isEmpty_iff] at hst; subst hst
        simp [matchg, bsOf]
      · simp at hm
  | cons p ps ih =>
    intro stack w a a' hlen hst hm ha
    have hp : p < ms.len := hlen p List.mem_cons_self
    have hlen' : ∀ x ∈ ps, x < ms.len := fun x hx => hlen x (List.mem_cons_of_mem _ hx)
    cases w with
    | nil => simp [maskAfter] at hm
    | cons s w =>
      rw [List.map_cons, matchg_cons]
      cases s with
      | skip =>
        rw [maskAfter] at hm
        have hsurv := ms.testBit_of_maskAfter _ _ _ _ _ hm ha
        have hbit : (ms.skipMask p).testBit j = true := by
          rw [Nat.testBit_and] at hsurv; exact (Bool.and_eq_true_iff.mp hsurv).2
        rw [(ms.skipMask_iff hp hj hc stack).mp hbit]
        simpa using ih _ _ _ _ hlen' hst hm ha
      | push =>
        rw [maskAfter] at hm
        have hsurv := ms.testBit_of_maskAfter _ _ _ _ _ hm ha
        have hbit : (ms.pushMask p).testBit j = true := by
          rw [Nat.testBit_and] at hsurv; exact (Bool.and_eq_true_iff.mp hsurv).2
        have h23 := (ms.testBit_pushMask hp hj hc).mp hbit
        have hst' : ms.StackOk j (p :: stack) := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨hp, h23⟩
          · exact hst x hx'
        rw [(ms.pushMask_iff hp hj hc stack).mp hbit]
        simpa using ih _ _ _ _ hlen' hst' hm ha
      | pop0 =>
        cases stack with
        | nil => rw [maskAfter] at hm; simp at hm
        | cons q rest =>
          rw [maskAfter] at hm
          obtain ⟨hq, hq23⟩ := hst q List.mem_cons_self
          have hsurv := ms.testBit_of_maskAfter _ _ _ _ _ hm ha
          have hbit : (ms.pop0Mask p q).testBit j = true := by
            rw [Nat.testBit_and] at hsurv; exact (Bool.and_eq_true_iff.mp hsurv).2
          rw [(ms.pop0Mask_iff hp hq hj hc hq23 rest).mp hbit]
          simpa using ih _ _ _ _ hlen'
            (fun x hx => hst x (List.mem_cons_of_mem _ hx)) hm ha
      | pop1 =>
        cases stack with
        | nil => rw [maskAfter] at hm; simp at hm
        | cons q rest =>
          rw [maskAfter] at hm
          obtain ⟨hq, hq23⟩ := hst q List.mem_cons_self
          have hsurv := ms.testBit_of_maskAfter _ _ _ _ _ hm ha
          have hbit : (ms.pop1Mask p q).testBit j = true := by
            rw [Nat.testBit_and] at hsurv; exact (Bool.and_eq_true_iff.mp hsurv).2
          rw [(ms.pop1Mask_iff hp hq hj hc hq23 rest).mp hbit]
          simpa using ih _ _ _ _ hlen'
            (fun x hx => hst x (List.mem_cons_of_mem _ hx)) hm ha

/-! ### From the walk to the certificate's obligation

Three steps remain between "the walk accepted" and the `hcert` hypothesis of
`kempeCoclosure_of_rank`: a trace matching a chromogram must *survive* the
descent by it, a covered subtree must then accept at the leaf that descent
reaches, and the witness is read back out with `matchg_of_maskAfter`. -/

/-- **Completeness of the descent**: a trace that matches the chromogram survives
descending by it. -/
theorem maskAfter_of_matchg (ms : Masks) (hc : ms.Consistent) {i : ℕ}
    (hi : i < ms.width) :
    ∀ (ps stack : List ℕ) (w : Chromogram) (a : ℕ),
      (∀ p ∈ ps, p < ms.len) → ms.StackOk i stack → a.testBit i = true →
      matchg (ms.bsOf i stack) (ps.map (fun p => ms.colourAt p i)) w = true →
      ∃ a', ms.maskAfter ps stack w a = some a' ∧ a'.testBit i = true := by
  intro ps
  induction ps with
  | nil =>
    intro stack w a hlen hst ha hm
    cases w with
    | cons s w => simp [matchg] at hm
    | nil =>
      refine ⟨a, ?_, ha⟩
      rw [maskAfter]
      have : ms.bsOf i stack = [] := by
        simpa [matchg] using hm
      have hst0 : stack = [] := by
        cases stack with
        | nil => rfl
        | cons q rest => simp [bsOf] at this
      subst hst0; simp
  | cons p ps ih =>
    intro stack w a hlen hst ha hm
    have hp : p < ms.len := hlen p List.mem_cons_self
    have hlen' : ∀ x ∈ ps, x < ms.len := fun x hx => hlen x (List.mem_cons_of_mem _ hx)
    cases w with
    | nil => simp [matchg] at hm
    | cons s w =>
      rw [List.map_cons, matchg_cons] at hm
      cases s with
      | skip =>
        cases hstep : matchStep (ms.colourAt p i) GramSymbol.skip (ms.bsOf i stack) with
        | none => rw [hstep] at hm; simp at hm
        | some lb' =>
          obtain ⟨heq, hbit⟩ := ms.step_skip hp hi hc stack hstep
          rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
          rw [maskAfter]
          exact ih _ _ _ hlen' hst (by simp [Nat.testBit_and, ha, hbit]) hm
      | push =>
        cases hstep : matchStep (ms.colourAt p i) GramSymbol.push (ms.bsOf i stack) with
        | none => rw [hstep] at hm; simp at hm
        | some lb' =>
          obtain ⟨heq, hbit, h23⟩ := ms.step_push hp hi hc stack hstep
          rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
          rw [maskAfter]
          refine ih _ _ _ hlen' ?_ (by simp [Nat.testBit_and, ha, hbit]) hm
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨hp, h23⟩
          · exact hst x hx'
      | pop0 =>
        cases stack with
        | nil =>
          rw [bsOf_nil] at hm
          cases hcol : ms.colourAt p i <;> rw [hcol] at hm <;> simp [matchStep] at hm
        | cons q rest =>
          obtain ⟨hq, hq23⟩ := hst q List.mem_cons_self
          cases hstep : matchStep (ms.colourAt p i) GramSymbol.pop0 (ms.bsOf i (q :: rest)) with
          | none => rw [hstep] at hm; simp at hm
          | some lb' =>
            obtain ⟨heq, hbit⟩ := ms.step_pop0 hp hq hi hc hq23 rest hstep
            rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
            rw [maskAfter]
            exact ih _ _ _ hlen' (fun x hx => hst x (List.mem_cons_of_mem _ hx))
              (by simp [Nat.testBit_and, ha, hbit]) hm
      | pop1 =>
        cases stack with
        | nil =>
          rw [bsOf_nil] at hm
          cases hcol : ms.colourAt p i <;> rw [hcol] at hm <;> simp [matchStep] at hm
        | cons q rest =>
          obtain ⟨hq, hq23⟩ := hst q List.mem_cons_self
          cases hstep : matchStep (ms.colourAt p i) GramSymbol.pop1 (ms.bsOf i (q :: rest)) with
          | none => rw [hstep] at hm; simp at hm
          | some lb' =>
            obtain ⟨heq, hbit⟩ := ms.step_pop1 hp hq hi hc hq23 rest hstep
            rw [hstep] at hm; simp only [Option.elim] at hm; subst heq
            rw [maskAfter]
            exact ih _ _ _ hlen' (fun x hx => hst x (List.mem_cons_of_mem _ hx))
              (by simp [Nat.testBit_and, ha, hbit]) hm

/-- **A covered subtree accepts at the leaf a descent reaches.** -/
theorem leafOk_of_maskAfter (ms : Masks) (leafOk : List ℕ → ℕ → Bool) {i : ℕ} :
    ∀ (ps stack : List ℕ) (w : Chromogram) (a a' : ℕ),
      ms.Covers leafOk ps stack a → ms.maskAfter ps stack w a = some a' →
      a'.testBit i = true → leafOk [] a' = true := by
  intro ps
  induction ps with
  | nil =>
    intro stack w a a' hcov hm ha
    cases w with
    | cons s w => simp [maskAfter] at hm
    | nil =>
      rw [maskAfter] at hm
      split at hm
      · next hst =>
        rw [List.isEmpty_iff] at hst; subst hst
        cases hm
        rw [covers_nil] at hcov
        exact hcov i ha rfl
      · simp at hm
  | cons p ps ih =>
    intro stack w a a' hcov hm ha
    rw [covers_cons] at hcov
    obtain ⟨hcs, hcp, hcq⟩ := hcov
    cases w with
    | nil => simp [maskAfter] at hm
    | cons s w =>
      cases s with
      | skip => rw [maskAfter] at hm; exact ih _ _ _ _ hcs hm ha
      | push => rw [maskAfter] at hm; exact ih _ _ _ _ hcp hm ha
      | pop0 =>
        cases stack with
        | nil => rw [maskAfter] at hm; simp at hm
        | cons q rest => rw [maskAfter] at hm; exact ih _ _ _ _ hcq.1 hm ha
      | pop1 =>
        cases stack with
        | nil => rw [maskAfter] at hm; simp at hm
        | cons q rest => rw [maskAfter] at hm; exact ih _ _ _ _ hcq.2 hm ha

end Masks

end FourColor

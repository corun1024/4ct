import FourColor.MaskCert

/-!
# The rank obligation at a leaf

At a leaf the certificate must justify every certified trace matching that
chromogram.  It does not need a witness for each: a witness ranking below the
*lowest* rank present serves all of them, since every other trace there ranks at
least as high.  So the whole obligation is one question — "is there a witness
below the lowest rank present?" — asked against masks that depend only on the
leaf's own mask.

`firstRank` walks the rank levels in order, stops at the first one that occurs
among the certified traces, and demands a witness below it.  `firstRank_sound`
is what the certificate needs out of it: a surviving witness, together with the
fact that every certified trace at the leaf ranks strictly above it.
-/

namespace FourColor

/-- Rank levels as `(traces of exactly this rank, witnesses below it)`, in
increasing order of rank. -/
abbrev RankPairs := List (ℕ × ℕ)

/-- Stop at the lowest rank present among `A`, and demand a witness below it. -/
def firstRank : RankPairs → ℕ → ℕ → Bool
  | [],           _, _ => false
  | (e, l) :: ps, A, a => if A &&& e == 0 then firstRank ps A a else a &&& l != 0

/-- A `Nat` is nonzero exactly when some bit of it is set. -/
theorem exists_testBit_of_ne_zero {x : ℕ} (h : x ≠ 0) : ∃ k, x.testBit k = true := by
  by_contra hcon
  push_neg at hcon
  exact h (Nat.eq_of_testBit_eq fun k => by simpa using hcon k)

/-- **What a passing leaf test yields.**  If `firstRank` accepts, the rank levels
split as `pre ++ (e, l) :: post` where no level in `pre` occurs among the
certified traces `A`, this level does occur, and a witness below it is still
live.  So `(e, l)` is the lowest rank present, and the witness ranks below it —
hence below every certified trace at this leaf. -/
theorem firstRank_sound :
    ∀ (ps : RankPairs) (A a : ℕ), firstRank ps A a = true →
      ∃ pre e l post, ps = pre ++ (e, l) :: post ∧
        (∀ q ∈ pre, A &&& q.1 = 0) ∧ A &&& e ≠ 0 ∧ ∃ j, (a &&& l).testBit j = true := by
  intro ps
  induction ps with
  | nil => intro A a h; simp [firstRank] at h
  | cons hd ps ih =>
    obtain ⟨e, l⟩ := hd
    intro A a h
    rw [firstRank] at h
    split at h
    · next hz =>
      obtain ⟨pre, e', l', post, hsplit, hpre, hne, hwit⟩ := ih A a h
      refine ⟨(e, l) :: pre, e', l', post, by rw [hsplit]; rfl, ?_, hne, hwit⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · simpa using hz
      · exact hpre q hq'
    · next hz =>
      exact ⟨[], e, l, ps, rfl, by simp, by simpa using hz,
        exists_testBit_of_ne_zero (by simpa using h)⟩


/-! ### The leaf test, and the witness it yields

`leafOk` is what the walk asks at each leaf.  It depends only on the leaf's mask,
which is why the walk machinery in `MaskCert` applies to it unchanged. -/

namespace Masks

/-- No certified trace matches this chromogram, or there is a witness below the
lowest rank present. -/
def leafTest (certMask : ℕ) (ps : RankPairs) (_stack : List ℕ) (a : ℕ) : Bool :=
  let A := a &&& certMask
  A == 0 || firstRank ps A a

/-- **The witness a passing leaf hands back.**  If some certified trace `i` is
live at this leaf, the test yields a live index `j` drawn from the witnesses
below the lowest rank present — and `i` is not itself below that rank. -/
theorem witness_of_leafTest {certMask : ℕ} {ps : RankPairs} {stack : List ℕ}
    {a i : ℕ} (h : leafTest certMask ps stack a = true)
    (hi : (a &&& certMask).testBit i = true) :
    ∃ pre e l post, ps = pre ++ (e, l) :: post ∧
      (∀ q ∈ pre, (a &&& certMask) &&& q.1 = 0) ∧
      ∃ j, a.testBit j = true ∧ l.testBit j = true := by
  rw [leafTest] at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with hz | hfr
  · exfalso; rw [hz] at hi; simp at hi
  · obtain ⟨pre, e, l, post, hsplit, hpre, _, j, hj⟩ := firstRank_sound ps _ a hfr
    rw [Nat.testBit_and] at hj
    exact ⟨pre, e, l, post, hsplit, hpre, j,
      (Bool.and_eq_true_iff.mp hj).1, (Bool.and_eq_true_iff.mp hj).2⟩

/-- **The certificate's obligation, discharged by one mask walk.**

`hwit` is what the generator must arrange: a witness drawn from the masks below
the lowest rank *present* is a colouring, or permutes into the certified set at a
strictly smaller rank than the trace being justified.  The "lowest rank present"
part reaches `hwit` as `hnp`: none of the earlier levels contains `i`.

Everything else is already proved — that a matching trace survives the descent
(`maskAfter_of_matchg`), that the walk checked the leaf it reaches
(`covers_of_walk`, `leafOk_of_maskAfter`), and that a survivor matches the
chromogram (`matchg_of_maskAfter`). -/
theorem hcert_of_walk (ms : Masks) (hc : ms.Consistent) (certMask : ℕ)
    (rps : RankPairs) {P S : List Color → Prop} {rank : List Color → ℕ}
    (hlw : ∀ e l, (e, l) ∈ rps → ∀ j, l.testBit j = true → j < ms.width)
    (hwit : ∀ (pre : RankPairs) (e l : ℕ) (post : RankPairs),
      rps = pre ++ (e, l) :: post →
      ∀ i, i < ms.width → certMask.testBit i = true →
        (∀ q ∈ pre, ∀ i', i' < ms.width → certMask.testBit i' = true →
          ms.traceOf i' = ms.traceOf i → q.1.testBit i' = false) →
      ∀ j, j < ms.width → l.testBit j = true →
        P (ms.traceOf j) ∨
          ∃ g : EdgePerm, S ((ms.traceOf j).map g) ∧
            rank ((ms.traceOf j).map g) < rank (ms.traceOf i))
    (hwalk : ms.walk (leafTest certMask rps) (List.range ms.len) [] ms.full = true)
    (hfull : ∀ i, i < ms.width → ms.full.testBit i = true) :
    ∀ i, i < ms.width → certMask.testBit i = true →
      ∀ w, matchg [] (ms.traceOf i) w = true →
        ∃ et', matchg [] et' w = true ∧
          (P et' ∨ ∃ g : EdgePerm, S (et'.map g) ∧ rank (et'.map g) < rank (ms.traceOf i)) := by
  intro i hi hcert w hmw
  have hps : ∀ p ∈ List.range ms.len, p < ms.len := fun p hp => List.mem_range.mp hp
  have hst0 : ms.StackOk i [] := by intro q hq; simp at hq
  have htr : (List.range ms.len).map (fun p => ms.colourAt p i) = ms.traceOf i := rfl
  obtain ⟨a', hma, hia⟩ :=
    ms.maskAfter_of_matchg hc hi (List.range ms.len) [] w ms.full hps hst0
      (hfull i hi) (by rw [htr]; exact hmw)
  have hcov := ms.covers_of_walk (leafTest certMask rps) _ _ _ hwalk
  have hleaf := ms.leafOk_of_maskAfter (leafTest certMask rps) _ _ _ _ _ hcov hma hia
  have hiA : (a' &&& certMask).testBit i = true := by
    rw [Nat.testBit_and, hia, hcert]; rfl
  obtain ⟨pre, e, l, post, hsplit, hpre, j, hja, hjl⟩ :=
    Masks.witness_of_leafTest hleaf hiA
  -- every certified index carrying this trace is live at the leaf, so none of
  -- them lies at an earlier rank level
  have hnp : ∀ q ∈ pre, ∀ i', i' < ms.width → certMask.testBit i' = true →
      ms.traceOf i' = ms.traceOf i → q.1.testBit i' = false := by
    intro q hq i' hi' hcert' htr'
    have hst0' : ms.StackOk i' [] := by intro r hr; simp at hr
    obtain ⟨a'', hma'', hia''⟩ :=
      ms.maskAfter_of_matchg hc hi' (List.range ms.len) [] w ms.full hps hst0'
        (hfull i' hi') (by
          show matchg [] ((List.range ms.len).map (fun p => ms.colourAt p i')) w = true
          rw [show (List.range ms.len).map (fun p => ms.colourAt p i') = ms.traceOf i' from rfl,
            htr']
          exact hmw)
    have ha : a'' = a' := by rw [hma''] at hma; exact Option.some.inj hma
    subst ha
    have hi'A : (a'' &&& certMask).testBit i' = true := by
      rw [Nat.testBit_and, hia'', hcert']; rfl
    have h0 : ((a'' &&& certMask) &&& q.1) = 0 := hpre q hq
    have hb : ((a'' &&& certMask) &&& q.1).testBit i' = false := by rw [h0]; simp
    rw [Nat.testBit_and, hi'A] at hb
    simpa using hb
  have hjw : j < ms.width := by
    refine hlw e l ?_ j hjl
    rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
  refine ⟨ms.traceOf j, ?_, hwit pre e l post hsplit i hi hcert hnp j hjw hjl⟩
  exact ms.matchg_of_maskAfter hc hjw (List.range ms.len) [] w ms.full a' hps
    (by intro q hq; simp at hq) hma hja

/-! ### The pruned walk

Once no certified trace is live, every leaf below passes trivially, so a
generated module cuts the walk there instead of at an empty mask.  The subtrees
the certified traces reach are a small part of the whole tree when the universe
is dominated by witnesses. -/

/-- The fuelled walk with the leaf test of `leafTest`, cut where no certified
trace remains live. -/
def walkPruned (ms : Masks) (certMask : ℕ) (ps : RankPairs) :
    ℕ → ℕ → List ℕ → ℕ → Bool
  | 0,        _, stack, a => !stack.isEmpty || leafTest certMask ps stack a
  | fuel + 1, p, stack, a =>
      if a &&& certMask == 0 then true else
        ms.walkPruned certMask ps fuel (p + 1) stack (a &&& ms.skipMask p) &&
        ms.walkPruned certMask ps fuel (p + 1) (p :: stack) (a &&& ms.pushMask p) &&
        (match stack with
         | [] => true
         | q :: rest =>
             ms.walkPruned certMask ps fuel (p + 1) rest (a &&& ms.pop0Mask p q) &&
             ms.walkPruned certMask ps fuel (p + 1) rest (a &&& ms.pop1Mask p q))

/-- With no certified trace live, the walk passes. -/
theorem walkFuel_of_land_certMask_zero (ms : Masks) (certMask : ℕ) (ps : RankPairs) :
    ∀ (fuel p : ℕ) (stack : List ℕ) (a : ℕ), a &&& certMask = 0 →
      ms.walkFuel (leafTest certMask ps) fuel p stack a = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro p stack a ha
    simp only [walkFuel, leafTest, ha, beq_self_eq_true, Bool.true_or, Bool.or_true]
  | succ fuel ih =>
    intro p stack a ha
    have hsub : ∀ x, (a &&& x) &&& certMask = 0 := by
      intro x
      apply Nat.eq_of_testBit_eq
      intro k
      have hk := congrArg (fun y => y.testBit k) ha
      simp only [Nat.testBit_and, Nat.zero_testBit] at hk ⊢
      revert hk
      cases a.testBit k <;> cases certMask.testBit k <;> cases x.testBit k <;> decide
    simp only [walkFuel]
    split
    · rfl
    · simp only [ih _ _ _ (hsub _), Bool.true_and]
      cases stack with
      | nil => rfl
      | cons q rest => simp only [ih _ _ _ (hsub _), Bool.and_self]

/-- **The pruned walk implies the full one.** -/
theorem walkFuel_of_pruned (ms : Masks) (certMask : ℕ) (ps : RankPairs) :
    ∀ (fuel p : ℕ) (stack : List ℕ) (a : ℕ),
      ms.walkPruned certMask ps fuel p stack a = true →
      ms.walkFuel (leafTest certMask ps) fuel p stack a = true := by
  intro fuel
  induction fuel with
  | zero => intro p stack a h; exact h
  | succ fuel ih =>
    intro p stack a h
    simp only [walkPruned] at h
    split at h
    · rename_i hz
      exact ms.walkFuel_of_land_certMask_zero certMask ps _ _ _ _ (by simpa using hz)
    · simp only [walkFuel]
      split
      · rfl
      · simp only [Bool.and_eq_true] at h ⊢
        refine ⟨⟨ih _ _ _ h.1.1, ih _ _ _ h.1.2⟩, ?_⟩
        cases stack with
        | nil => rfl
        | cons q rest =>
          simp only [Bool.and_eq_true] at h ⊢
          exact ⟨ih _ _ _ h.2.1, ih _ _ _ h.2.2⟩

end Masks

end FourColor

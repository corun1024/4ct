import FourColor.MaskWit
import FourColor.Bulk.Chords

/-!
# The mask walk with chords that settle traces

The plain walk visits every chromogram prefix some certified trace reaches.
Most of those prefixes are wasted: for most traces and most chromograms a
single chord of the chromogram already supplies a witness — the flip of the
trace along that chord, or along the arc it encloses — and the certificate
only has to work where no single chord does.

So the walk here carries the certified set still to be justified, `c`, and
each closed chord `(q, p)` removes from it the traces `ok q p` names: the
traces some flip along that chord settles.  A subtree with nothing left to
justify is cut.  Soundness is by descent: at the leaf a chromogram reaches, a
trace still in `c` is handled by the leaf test as before, and a trace removed
from `c` was removed by a chord of that chromogram, which `hok` turns into a
witness.

## Main results

* `walkC`, `walkCF` — the walk, over a position list and with fuel.
* `leafTest_of_walkC` — the leaf test holds at every leaf a descent reaches.
* `certAfter_spec` — a trace dropped during a descent was dropped by a chord.
* `hcert_of_walkC` — the certificate obligation from one such walk.
* `coclosure_of_walkC` — every certified trace lies in the Kempe co-closure.
-/

namespace FourColor
namespace Masks

/-! ### The walk -/

/-- The walk carrying the certified set `c` still to justify.  `ok q p` names
the certified traces a closed chord `(q, p)` settles. -/
def walkC (ms : Masks) (ok : ℕ → ℕ → ℕ) (rps : RankPairs) :
    List ℕ → List ℕ → ℕ → ℕ → Bool
  | [],      stack, a, c => !stack.isEmpty || leafTest c rps stack a
  | p :: ps, stack, a, c =>
      if a &&& c == 0 then true else
        ms.walkC ok rps ps stack (a &&& ms.skipMask p) c &&
        ms.walkC ok rps ps (p :: stack) (a &&& ms.pushMask p) c &&
        (match stack with
         | [] => true
         | q :: rest =>
             ms.walkC ok rps ps rest (a &&& ms.pop0Mask p q) (c ^^^ (c &&& ok q p)) &&
             ms.walkC ok rps ps rest (a &&& ms.pop1Mask p q) (c ^^^ (c &&& ok q p)))

/-- The same walk with fuel and a starting position: the shape a generated
module emits. -/
def walkCF (ms : Masks) (ok : ℕ → ℕ → ℕ) (rps : RankPairs) :
    ℕ → ℕ → List ℕ → ℕ → ℕ → Bool
  | 0,        _, stack, a, c => !stack.isEmpty || leafTest c rps stack a
  | fuel + 1, p, stack, a, c =>
      if a &&& c == 0 then true else
        ms.walkCF ok rps fuel (p + 1) stack (a &&& ms.skipMask p) c &&
        ms.walkCF ok rps fuel (p + 1) (p :: stack) (a &&& ms.pushMask p) c &&
        (match stack with
         | [] => true
         | q :: rest =>
             ms.walkCF ok rps fuel (p + 1) rest (a &&& ms.pop0Mask p q) (c ^^^ (c &&& ok q p)) &&
             ms.walkCF ok rps fuel (p + 1) rest (a &&& ms.pop1Mask p q) (c ^^^ (c &&& ok q p)))

theorem walkCF_eq (ms : Masks) (ok : ℕ → ℕ → ℕ) (rps : RankPairs) :
    ∀ (fuel p : ℕ) (stack : List ℕ) (a c : ℕ),
      ms.walkCF ok rps fuel p stack a c = ms.walkC ok rps (List.range' p fuel) stack a c := by
  intro fuel
  induction fuel with
  | zero => intro p stack a c; rfl
  | succ fuel ih =>
    intro p stack a c
    rw [List.range'_succ]
    simp only [walkCF, walkC, ih]

/-! ### The certified set along a descent -/

/-- The certified set after descending by a chromogram: each closed chord
removes the traces it settles.  Where the chromogram does not fit, the set is
left alone (the mask descent fails there anyway). -/
def certAfter (ok : ℕ → ℕ → ℕ) : List ℕ → List ℕ → Chromogram → ℕ → ℕ
  | _ :: ps, stack,     .skip :: w, c => certAfter ok ps stack w c
  | p :: ps, stack,     .push :: w, c => certAfter ok ps (p :: stack) w c
  | p :: ps, q :: rest, .pop0 :: w, c => certAfter ok ps rest w (c ^^^ (c &&& ok q p))
  | p :: ps, q :: rest, .pop1 :: w, c => certAfter ok ps rest w (c ^^^ (c &&& ok q p))
  | _,       _,         _,          c => c

theorem testBit_remove (c x i : ℕ) :
    (c ^^^ (c &&& x)).testBit i = (c.testBit i && !x.testBit i) := by
  simp only [Nat.testBit_xor, Nat.testBit_and]
  cases c.testBit i <;> cases x.testBit i <;> rfl

/-- The certified set only shrinks. -/
theorem testBit_of_certAfter (ok : ℕ → ℕ → ℕ) {i : ℕ} :
    ∀ (ps stack : List ℕ) (w : Chromogram) (c : ℕ),
      (certAfter ok ps stack w c).testBit i = true → c.testBit i = true := by
  intro ps
  induction ps with
  | nil => intro stack w c h; simpa [certAfter] using h
  | cons p ps ih =>
    intro stack w c h
    cases w with
    | nil => simpa [certAfter] using h
    | cons s w =>
      cases s with
      | skip => exact ih _ _ _ (by simpa [certAfter] using h)
      | push => exact ih _ _ _ (by simpa [certAfter] using h)
      | pop0 =>
        cases stack with
        | nil => simpa [certAfter] using h
        | cons q rest =>
          have := ih _ _ _ (by simpa [certAfter] using h)
          rw [testBit_remove] at this
          exact (Bool.and_eq_true_iff.mp this).1
      | pop1 =>
        cases stack with
        | nil => simpa [certAfter] using h
        | cons q rest =>
          have := ih _ _ _ (by simpa [certAfter] using h)
          rw [testBit_remove] at this
          exact (Bool.and_eq_true_iff.mp this).1

/-- **A trace dropped during a descent was dropped by a chord of the
chromogram.** -/
theorem certAfter_spec (ok : ℕ → ℕ → ℕ) {x : ℕ} :
    ∀ (w : Chromogram) (i : ℕ) (st : List ℕ) (cs : List (ℕ × ℕ)) (c : ℕ),
      chordsAux i st w = some cs → c.testBit x = true →
      (certAfter ok (List.range' i w.length) st w c).testBit x = false →
      ∃ qp ∈ cs, (ok qp.1 qp.2).testBit x = true := by
  intro w
  induction w with
  | nil =>
    intro i st cs c hcs hc hafter
    cases st with
    | nil => simp [certAfter] at hafter; rw [hc] at hafter; exact absurd hafter (by simp)
    | cons a st => simp [chordsAux] at hcs
  | cons s w ih =>
    intro i st cs c hcs hc hafter
    simp only [List.length_cons, List.range'_succ] at hafter
    cases s with
    | skip =>
      simp only [chordsAux] at hcs
      simp only [certAfter] at hafter
      exact ih _ _ _ _ hcs hc hafter
    | push =>
      simp only [chordsAux] at hcs
      simp only [certAfter] at hafter
      exact ih _ _ _ _ hcs hc hafter
    | pop0 =>
      cases st with
      | nil => simp [chordsAux] at hcs
      | cons a st =>
        simp only [chordsAux, Option.map_eq_some_iff] at hcs
        obtain ⟨cs', hcs', rfl⟩ := hcs
        simp only [certAfter] at hafter
        by_cases hok : (ok a i).testBit x = true
        · exact ⟨(a, i), List.mem_cons_self, hok⟩
        · have hc' : (c ^^^ (c &&& ok a i)).testBit x = true := by
            rw [testBit_remove, hc]; simpa using hok
          obtain ⟨qp, hqp, h⟩ := ih _ _ _ _ hcs' hc' hafter
          exact ⟨qp, List.mem_cons_of_mem _ hqp, h⟩
    | pop1 =>
      cases st with
      | nil => simp [chordsAux] at hcs
      | cons a st =>
        simp only [chordsAux, Option.map_eq_some_iff] at hcs
        obtain ⟨cs', hcs', rfl⟩ := hcs
        simp only [certAfter] at hafter
        by_cases hok : (ok a i).testBit x = true
        · exact ⟨(a, i), List.mem_cons_self, hok⟩
        · have hc' : (c ^^^ (c &&& ok a i)).testBit x = true := by
            rw [testBit_remove, hc]; simpa using hok
          obtain ⟨qp, hqp, h⟩ := ih _ _ _ _ hcs' hc' hafter
          exact ⟨qp, List.mem_cons_of_mem _ hqp, h⟩

/-! ### The walk covers every leaf a descent reaches -/

/-- With nothing left to justify, the leaf test passes. -/
theorem leafTest_of_land_zero {c : ℕ} (rps : RankPairs) (stack : List ℕ) {a : ℕ}
    (h : a &&& c = 0) : leafTest c rps stack a = true := by
  simp only [leafTest, h, beq_self_eq_true, Bool.true_or]

/-- **The leaf test holds, for the certified set the descent leaves, at every
leaf a descent reaches.** -/
theorem leafTest_of_walkC (ms : Masks) (ok : ℕ → ℕ → ℕ) (rps : RankPairs) :
    ∀ (ps stack : List ℕ) (a c : ℕ) (w : Chromogram) (a' : ℕ),
      ms.walkC ok rps ps stack a c = true → ms.maskAfter ps stack w a = some a' →
      leafTest (certAfter ok ps stack w c) rps [] a' = true := by
  intro ps
  induction ps with
  | nil =>
    intro stack a c w a' hw hm
    cases w with
    | cons s w => simp [maskAfter] at hm
    | nil =>
      rw [maskAfter] at hm
      split at hm
      · next hst =>
        rw [List.isEmpty_iff] at hst; subst hst
        cases hm
        simp only [walkC, List.isEmpty_nil, Bool.not_true, Bool.false_or] at hw
        simpa [certAfter] using hw
      · simp at hm
  | cons p ps ih =>
    intro stack a c w a' hw hm
    by_cases hz : a &&& c = 0
    · -- nothing to justify below: the leaf's certified set is empty
      apply leafTest_of_land_zero
      apply Nat.eq_of_testBit_eq
      intro j
      have hj := congrArg (fun x => x.testBit j) hz
      simp only [Nat.testBit_and, Nat.zero_testBit] at hj ⊢
      cases ha : a'.testBit j
      · rfl
      · cases hc : (certAfter ok (p :: ps) stack w c).testBit j
        · rfl
        · have h1 := ms.testBit_of_maskAfter _ _ _ _ _ hm ha
          have h2 := testBit_of_certAfter ok _ _ _ _ hc
          rw [h1, h2] at hj
          exact absurd hj (by simp)
    · have hzb : (a &&& c == 0) = false := by simpa using hz
      simp only [walkC, hzb, Bool.false_eq_true, ite_false, Bool.and_eq_true_iff] at hw
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw
      cases w with
      | nil => simp [maskAfter] at hm
      | cons s w =>
        cases s with
        | skip =>
          rw [maskAfter] at hm
          simpa [certAfter] using ih _ _ _ _ _ h1 hm
        | push =>
          rw [maskAfter] at hm
          simpa [certAfter] using ih _ _ _ _ _ h2 hm
        | pop0 =>
          cases stack with
          | nil => rw [maskAfter] at hm; simp at hm
          | cons q rest =>
            rw [maskAfter] at hm
            simp only [Bool.and_eq_true_iff] at h3
            simpa [certAfter] using ih _ _ _ _ _ h3.1 hm
        | pop1 =>
          cases stack with
          | nil => rw [maskAfter] at hm; simp at hm
          | cons q rest =>
            rw [maskAfter] at hm
            simp only [Bool.and_eq_true_iff] at h3
            simpa [certAfter] using ih _ _ _ _ _ h3.2 hm

/-! ### List bookkeeping -/

theorem getD_append_length {α : Type*} (d : α) :
    ∀ (pre : List α) (q : α) (post : List α), (pre ++ q :: post).getD pre.length d = q := by
  intro pre
  induction pre with
  | nil => intro q post; rfl
  | cons x pre ih => intro q post; simpa using ih q post

/-- An element sitting before another split point lies in that split's prefix. -/
theorem mem_pre_of_length_lt {α : Type*} :
    ∀ (pre' : List α) (q' : α) (post' pre : List α) (x : α) (post : List α),
      pre' ++ q' :: post' = pre ++ x :: post → pre'.length < pre.length → q' ∈ pre := by
  intro pre'
  induction pre' with
  | nil =>
    intro q' post' pre x post h hl
    cases pre with
    | nil => simp at hl
    | cons y pre =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      rw [h.1]; exact List.mem_cons_self
  | cons y pre' ih =>
    intro q' post' pre x post h hl
    cases pre with
    | nil => simp at hl
    | cons z pre =>
      simp only [List.cons_append, List.cons.injEq] at h
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hl
      exact List.mem_cons_of_mem _ (ih q' post' pre x post h.2 hl)

/-! ### The certificate obligation -/

/-- **The certificate's obligation, discharged by one chord-aware walk.**

`hlvl` pins the rank of a certified trace to the level naming it, `hcov` says
every certified trace has a level, `hwit` is the witness-level obligation of
`hwit_of_buildRank`, and `hok` is what the settling masks promise: a trace
`ok q p` names has, for every chromogram with chord `(q, p)` it matches, a
witness matching that chromogram. -/
theorem hcert_of_walkC (ms : Masks) (hc : ms.Consistent) (certMask : ℕ)
    (ok : ℕ → ℕ → ℕ) (rps : RankPairs) {P S : List Color → Prop} {rank : List Color → ℕ}
    (hlw : ∀ e l, (e, l) ∈ rps → ∀ j, l.testBit j = true → j < ms.width)
    (hlvl : ∀ (pre : RankPairs) (q : ℕ × ℕ) (post : RankPairs), rps = pre ++ q :: post →
      ∀ i, i < ms.width → certMask.testBit i = true → q.1.testBit i = true →
        rank (ms.traceOf i) = pre.length + 1)
    (hcov : ∀ i, i < ms.width → certMask.testBit i = true → ∃ q ∈ rps, q.1.testBit i = true)
    (hS : ∀ i, i < ms.width → certMask.testBit i = true → S (ms.traceOf i))
    (hwit : ∀ (pre : RankPairs) (e l : ℕ) (post : RankPairs),
      rps = pre ++ (e, l) :: post →
      ∀ j, j < ms.width → l.testBit j = true →
        P (ms.traceOf j) ∨
          ∃ g : EdgePerm, ∃ q ∈ pre, ms.AtLevel certMask q.1 ((ms.traceOf j).map g))
    (hok : ∀ q p i, i < ms.width → certMask.testBit i = true → (ok q p).testBit i = true →
      ∀ (w : Chromogram) (cs : List (ℕ × ℕ)), matchg [] (ms.traceOf i) w = true →
        chords w = some cs → (q, p) ∈ cs →
        ∃ et', matchg [] et' w = true ∧
          (P et' ∨ ∃ g : EdgePerm, S (et'.map g) ∧ rank (et'.map g) < rank (ms.traceOf i)))
    (hwalk : ms.walkC ok rps (List.range ms.len) [] ms.full certMask = true)
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
  have hleaf := ms.leafTest_of_walkC ok rps _ _ _ _ w _ hwalk hma
  set c' := certAfter ok (List.range ms.len) [] w certMask with hc'
  by_cases hci : c'.testBit i = true
  · -- still to justify at the leaf: the leaf test names a witness
    have hiA : (a' &&& c').testBit i = true := by
      rw [Nat.testBit_and, hia, hci]; rfl
    obtain ⟨pre, e, l, post, hsplit, hpre, j, hja, hjl⟩ :=
      Masks.witness_of_leafTest hleaf hiA
    have hjw : j < ms.width := by
      refine hlw e l ?_ j hjl
      rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
    have hjm : matchg [] (ms.traceOf j) w = true :=
      ms.matchg_of_maskAfter hc hjw (List.range ms.len) [] w ms.full a' hps
        (by intro q hq; simp at hq) hma hja
    refine ⟨ms.traceOf j, hjm, ?_⟩
    rcases hwit pre e l post hsplit j hjw hjl with hgood | ⟨g, q, hq, hat⟩
    · exact Or.inl hgood
    obtain ⟨i', hi', hc', hb', ht'⟩ := hat
    refine Or.inr ⟨g, ?_, ?_⟩
    · rw [← ht']; exact hS i' hi' hc'
    · -- the witness ranks at the level of `q`, inside `pre`
      obtain ⟨pre₁, pre₂, rfl⟩ := List.append_of_mem hq
      have hsplit' : rps = pre₁ ++ q :: (pre₂ ++ (e, l) :: post) := by
        rw [hsplit, List.append_assoc, List.cons_append]
      have hrw : rank ((ms.traceOf j).map g) = pre₁.length + 1 := by
        rw [← ht']; exact hlvl pre₁ q _ hsplit' i' hi' hc' hb'
      -- the trace being justified ranks at or beyond the whole of `pre`
      obtain ⟨q', hq', hb⟩ := hcov i hi hcert
      obtain ⟨pre', post', hsplit''⟩ := List.append_of_mem hq'
      have hri : rank (ms.traceOf i) = pre'.length + 1 :=
        hlvl pre' q' post' hsplit'' i hi hcert hb
      have hge : (pre₁ ++ q :: pre₂).length ≤ pre'.length := by
        by_contra hlt
        have hlt' : pre'.length < (pre₁ ++ q :: pre₂).length := by omega
        have hmem : q' ∈ pre₁ ++ q :: pre₂ :=
          mem_pre_of_length_lt pre' q' post' _ (e, l) post (hsplit''.symm.trans hsplit) hlt'
        have h0 := hpre q' hmem
        have hb0 := congrArg (fun x => x.testBit i) h0
        simp only [Nat.testBit_and, hiA, Bool.true_and, Nat.zero_testBit] at hb0
        rw [hb] at hb0; exact absurd hb0 (by simp)
      rw [hrw, hri]
      simp only [List.length_append, List.length_cons] at hge
      omega
  · -- dropped on the way down: a chord of `w` settles it
    have hlen : w.length = ms.len := by
      have := matchg_length (ms.traceOf i) [] w hmw
      simpa [traceOf] using this
    obtain ⟨cs, hcs⟩ := chords_isSome_of_matchg hmw
    have hafter : (certAfter ok (List.range' 0 w.length) [] w certMask).testBit i = false := by
      rw [hlen, ← List.range_eq_range']
      simpa using hci
    obtain ⟨qp, hqp, hokb⟩ := certAfter_spec ok w 0 [] cs certMask hcs hcert hafter
    exact hok qp.1 qp.2 i hi hcert hokb w cs hmw hcs hqp

/-- **Every certified trace lies in the Kempe co-closure**, from a chord-aware
walk. -/
theorem coclosure_of_walkC (ms : Masks) (hc : ms.Consistent) (certMask : ℕ)
    (ok : ℕ → ℕ → ℕ) (rps : RankPairs) {P : List Color → Prop} (rank : List Color → ℕ)
    (hlw : ∀ e l, (e, l) ∈ rps → ∀ j, l.testBit j = true → j < ms.width)
    (hlvl : ∀ (pre : RankPairs) (q : ℕ × ℕ) (post : RankPairs), rps = pre ++ q :: post →
      ∀ i, i < ms.width → certMask.testBit i = true → q.1.testBit i = true →
        rank (ms.traceOf i) = pre.length + 1)
    (hcov : ∀ i, i < ms.width → certMask.testBit i = true → ∃ q ∈ rps, q.1.testBit i = true)
    (hwit : ∀ (pre : RankPairs) (e l : ℕ) (post : RankPairs),
      rps = pre ++ (e, l) :: post →
      ∀ j, j < ms.width → l.testBit j = true →
        P (ms.traceOf j) ∨
          ∃ g : EdgePerm, ∃ q ∈ pre, ms.AtLevel certMask q.1 ((ms.traceOf j).map g))
    (hok : ∀ q p i, i < ms.width → certMask.testBit i = true → (ok q p).testBit i = true →
      ∀ (w : Chromogram) (cs : List (ℕ × ℕ)), matchg [] (ms.traceOf i) w = true →
        chords w = some cs → (q, p) ∈ cs →
        ∃ et', matchg [] et' w = true ∧
          (P et' ∨ ∃ g : EdgePerm, ms.Cert certMask (et'.map g) ∧
            rank (et'.map g) < rank (ms.traceOf i)))
    (hwalk : ms.walkC ok rps (List.range ms.len) [] ms.full certMask = true)
    (hfull : ∀ i, i < ms.width → ms.full.testBit i = true) :
    ∀ et, ms.Cert certMask et → KempeCoclosure P et := by
  intro et hcert
  refine kempeCoclosure_of_rank (P := P) (S := ms.Cert certMask) rank ?_ hcert
  rintro et' ⟨i, hi, hcm, rfl⟩ w hmw
  exact ms.hcert_of_walkC hc certMask ok rps (P := P) (S := ms.Cert certMask) (rank := rank)
    hlw hlvl hcov (fun i hi hc => ⟨i, hi, hc, rfl⟩) hwit hok hwalk hfull i hi hcm w hmw

end Masks
end FourColor

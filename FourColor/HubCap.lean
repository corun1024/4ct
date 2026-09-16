import FourColor.Discharge

/-!
# Hubcaps: ruling out a part by discharging

A *hubcap* is a set of constraints on the net charge transferred across the
edges around a hub.  Checking a hubcap against a part combines the two halves
of the proof: the discharge rules bound each transfer, and the reducibility
check rules out the parts in which a transfer could be too large.  If every
edge around the hub is covered by a constraint, and the constraints add up to
at most the hub's initial charge, then no dart of a minimal counterexample can
fit the part.

The reducibility check is a parameter `redp` here — it is `redpart` of
`FourColor.RedPart`, but the two halves are only tied together in the
presentation scripts, and keeping it abstract avoids a recursion between the
two files, exactly as in the reference.

## Main definitions

* `Hubcap` — the constraints, as a compressed list.
* `checkDbound1`, `checkDbound2`, `check2Dbound2` — the bound checks for one
  source, one target and two target edges.
* `hubcapCover`, `hubcapFit` — the two halves of the hubcap check.

## Main results

* `Hypermap.checkDbound1_le`, `Hypermap.checkDbound2_le`,
  `Hypermap.check2Dbound2_le` — the checks bound the transfers.
* `Hypermap.not_exactFitp_of_hubcap` — a part passing a covering hubcap check
  fits no positively charged dart.
-/

namespace FourColor

/-- A hubcap: a list of constraints on the net charge transfers around a hub.
`one j b` constrains the transfer at `face^[j]` of the hub dart to be at most
`b`; `two j₁ j₂ b` constrains the sum of the transfers at two such darts. -/
inductive Hubcap
  | nil
  | one (j : ℕ) (b : ℤ) (hc : Hubcap)
  | two (j₁ j₂ : ℕ) (b : ℤ) (hc : Hubcap)
  deriving Repr

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D}

omit [Finite D] in
/-- A part met with a rule that fits still fits exactly. -/
theorem exactFitp_meet {x : D} {p r : Part} (hp : G.ExactFitp x p) (hr : G.Fitp x r) :
    G.ExactFitp x (p.meet r) :=
  ⟨by rw [Part.size_meet]; exact hp.1, G.fitp_meet p r x hp.2 hr⟩

omit [Finite D] in
/-- At most every rule of a list fits. -/
theorem dbound1_le_length (rs : List Part) (x : D) : G.dbound1 rs x ≤ rs.length :=
  List.countP_le_length

end Hypermap

/-! ### Bounding the number of source rules that apply -/

/-- The recursion behind `checkDbound1`: `ns` is the bound still to be proved
for the rules `rs`, `p` the part specialised by the rules already assumed to
match, and the first argument a termination count. -/
def checkDbound1Rec (redp : Part → Bool) : ℕ → Part → List Part → ℕ → Bool
  | 0, _, _, _ => false
  | _ + 1, _, [], _ => true
  | m + 1, p, r :: rs, ns =>
      if rs.length < ns then true
      else
        let p' := p.meet r
        let sd := sortDrules p' rs
        (match ns - sd.nbForced with
          | 0 => redp p'
          | ns' + 1 => checkDbound1Rec redp m p' sd.straddling ns') &&
          checkDbound1Rec redp m p rs ns

/-- At most `ns` of the source rules of `rf` apply at a dart fitting `p`. -/
def checkDbound1 {conv : Part → PRange × Part} {nhub : ℕ} (redp : Part → Bool)
    (rf : DruleFork conv nhub) (p : Part) (ns : ℕ) : Bool :=
  checkDbound1Rec redp (rf.source.length + 1) p rf.source ns

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {redp : Part → Bool}

omit [Finite D] in
/-- Soundness of the recursion behind `checkDbound1`. -/
theorem checkDbound1Rec_le (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q) :
    ∀ (m ns : ℕ) (rs : List Part) (p : Part) (x : D), G.ExactFitp x p →
      checkDbound1Rec redp m p rs ns = true → G.dbound1 rs x ≤ ns := by
  intro m
  induction m with
  | zero => intro ns rs p x _ h; simp [checkDbound1Rec] at h
  | succ m ih =>
    intro ns rs p x hfit h
    match rs with
    | [] => simp [dbound1]
    | r :: rs =>
      rw [checkDbound1Rec] at h
      split at h
      · rename_i hlt
        have := G.dbound1_le_length (r :: rs) x
        simp only [List.length_cons] at this
        omega
      · rw [Bool.and_eq_true] at h
        obtain ⟨h₁, h₂⟩ := h
        by_cases hr : G.Fitp x r
        · have hfit' : G.ExactFitp x (p.meet r) := exactFitp_meet hfit hr
          have hsort := G.sort_dbound1_eq hfit'.2 rs
          rcases hd : ns - (sortDrules (p.meet r) rs).nbForced with _ | ns₁
          · rw [hd] at h₁
            exact absurd hfit' (hredp x _ h₁)
          · rw [hd] at h₁
            have hle := ih ns₁ _ _ x hfit' h₁
            rw [G.dbound1_cons_pos hr]
            omega
        · rw [G.dbound1_cons_neg hr]
          exact ih ns rs p x hfit h₂

omit [Finite D] in
/-- At most `ns` source rules apply at a dart that fits `p` exactly. -/
theorem checkDbound1_le {conv : Part → PRange × Part} {nhub : ℕ} {rf : DruleFork conv nhub}
    (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q) {x : D} {p : Part}
    {ns : ℕ} (hfit : G.ExactFitp x p) (h : checkDbound1 redp rf p ns = true) :
    G.dbound1 rf.source x ≤ ns :=
  checkDbound1Rec_le hredp _ ns _ p x hfit h

end Hypermap

/-! ### Excluded rules -/

/-- The part `p` forces one of the rules of `ru`. -/
def checkUnfit (p : Part) : List Part → Bool
  | [] => false
  | r :: ru => if p.cmp r = .subset then true else checkUnfit p ru

/-- `checkUnfit` and a pruning, in one pass: `none` if `p` forces one of the
rules of `ru`, and otherwise the rules of `ru` that `p` straddles.

A rule disjoint from `p` is disjoint from every part refining `p`, so it can
never be forced further down the search and carrying it on would only cost the
comparison again at every node below.  The comparison that prunes it is the one
`checkUnfit` already makes, so the pruning is free. -/
def pruneUnfit (p : Part) : List Part → Option (List Part)
  | [] => some []
  | r :: ru =>
      match p.cmp r with
      | .subset => none
      | .disjoint => pruneUnfit p ru
      | .straddle =>
          match pruneUnfit p ru with
          | none => none
          | some ru' => some (r :: ru')

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D}

omit [Finite D] in
/-- A dart fitting `p` at which none of the rules of `ru` applies witnesses
that `p` forces none of them. -/
theorem checkUnfit_eq_false {x : D} {p : Part} (hp : G.Fitp x p) :
    ∀ ru : List Part, G.dbound1 ru x = 0 → checkUnfit p ru = false := by
  intro ru
  induction ru with
  | nil => intro _; rfl
  | cons r ru ih =>
    intro h0
    have hr : ¬ G.Fitp x r := by
      intro hr
      rw [G.dbound1_cons_pos hr] at h0
      omega
    rw [G.dbound1_cons_neg hr] at h0
    rw [checkUnfit]
    split
    · rename_i hsub
      exact absurd (G.fitp_cmp_subset p r x hsub hp) hr
    · exact ih h0

omit [Finite D] in
/-- A dart fitting `p` at which none of the rules of `ru` applies witnesses
that `p` forces none of them, and the rules the pruning keeps still do not
apply at that dart. -/
theorem pruneUnfit_eq_some {x : D} {p : Part} (hp : G.Fitp x p) :
    ∀ ru : List Part, G.dbound1 ru x = 0 →
      ∃ ru', pruneUnfit p ru = some ru' ∧ G.dbound1 ru' x = 0 := by
  intro ru
  induction ru with
  | nil => intro _; exact ⟨[], rfl, by simp [dbound1]⟩
  | cons r ru ih =>
    intro h0
    have hr : ¬ G.Fitp x r := by
      intro hr
      rw [G.dbound1_cons_pos hr] at h0
      omega
    rw [G.dbound1_cons_neg hr] at h0
    obtain ⟨ru', hru', h0'⟩ := ih h0
    rcases hcmp : p.cmp r with _ | _ | _
    · exact ⟨ru', by simpa only [pruneUnfit, hcmp] using hru', h0'⟩
    · exact ⟨r :: ru', by simp only [pruneUnfit, hcmp, hru'],
        by rw [G.dbound1_cons_neg hr]; exact h0'⟩
    · exact absurd (G.fitp_cmp_subset p r x hcmp hp) hr

end Hypermap

/-! ### Bounding the net transfer across one edge -/

/-- The recursion behind `checkDbound2`: `rt` are the target rules still to be
considered, `rs` the source rules, `ru` the target rules already assumed not to
match, and `nt` the bound still to be proved. -/
def checkDbound2Rec (redp : Part → Bool) :
    ℕ → Part → List Part → List Part → List Part → ℕ → Bool
  | 0, _, _, _, _, _ => false
  | _ + 1, _, [], _, _, _ => true
  | m + 1, p, r :: rt, rs, ru, nt =>
      if rt.length < nt then true
      else
        (match pruneUnfit (p.meet r) ru with
          | none => true
          | some ru' =>
            match (sortDrules (p.meet r) rs).nbForced + nt
                - (sortDrules (p.meet r) rt).nbForced with
            | 0 => redp (p.meet r)
            | nt' + 1 =>
                checkDbound2Rec redp m (p.meet r) (sortDrules (p.meet r) rt).straddling
                  (sortDrules (p.meet r) rs).straddling ru' nt') &&
          checkDbound2Rec redp m p rt rs (r :: ru) nt

/-- The net charge transferred to a dart fitting `p` exactly is at most `b`. -/
def checkDbound2 {conv : Part → PRange × Part} {nhub : ℕ} (redp : Part → Bool)
    (rf : DruleFork conv nhub) (p : Part) (b : ℤ) : Bool :=
  let sdt := sortDrules p rf.target
  let sds := sortDrules p rf.source
  match (sds.nbForced : ℤ) - sdt.nbForced + b with
  | .ofNat nt =>
      checkDbound2Rec redp (sdt.straddling.length + 2) p sdt.straddling sds.straddling [] nt
  | .negSucc _ => false

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {redp : Part → Bool}

omit [Finite D] in
/-- Soundness of the recursion behind `checkDbound2`. -/
theorem checkDbound2Rec_le (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q) :
    ∀ (m nt : ℕ) (rt rs ru : List Part) (p : Part) (x : D), G.dbound1 ru x = 0 →
      G.ExactFitp x p → checkDbound2Rec redp m p rt rs ru nt = true →
      G.dbound1 rt x ≤ nt + G.dbound1 rs x := by
  intro m
  induction m with
  | zero => intro nt rt rs ru p x _ _ h; simp [checkDbound2Rec] at h
  | succ m ih =>
    intro nt rt rs ru p x hru hfit h
    match rt with
    | [] => simp [dbound1]
    | r :: rt =>
      rw [checkDbound2Rec] at h
      split at h
      · rename_i hlt
        have := G.dbound1_le_length (r :: rt) x
        simp only [List.length_cons] at this
        omega
      · rw [Bool.and_eq_true] at h
        obtain ⟨h₁, h₂⟩ := h
        by_cases hr : G.Fitp x r
        · have hfit' : G.ExactFitp x (p.meet r) := exactFitp_meet hfit hr
          obtain ⟨ru', hpr, hru'⟩ := pruneUnfit_eq_some hfit'.2 ru hru
          rw [hpr] at h₁
          have hsortt := G.sort_dbound1_eq hfit'.2 rt
          have hsorts := G.sort_dbound1_eq hfit'.2 rs
          rcases hd : (sortDrules (p.meet r) rs).nbForced + nt
              - (sortDrules (p.meet r) rt).nbForced with _ | nt₁
          · rw [hd] at h₁
            exact absurd hfit' (hredp x _ h₁)
          · rw [hd] at h₁
            have hle := ih nt₁ _ _ ru' _ x hru' hfit' h₁
            rw [G.dbound1_cons_pos hr]
            omega
        · rw [G.dbound1_cons_neg hr]
          refine ih nt rt rs (r :: ru) p x ?_ hfit h₂
          rw [G.dbound1_cons_neg hr]
          exact hru

omit [Finite D] in
/-- The net charge transferred to a dart fitting `p` exactly is at most `b`. -/
theorem checkDbound2_le {conv : Part → PRange × Part} {nhub : ℕ} {rf : DruleFork conv nhub}
    (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q) {x : D} {p : Part}
    {b : ℤ} (hfit : G.ExactFitp x p) (h : checkDbound2 redp rf p b = true) :
    G.dbound2 rf.target rf.source x ≤ b := by
  rw [checkDbound2] at h
  have hsortt := G.sort_dbound1_eq hfit.2 rf.target
  have hsorts := G.sort_dbound1_eq hfit.2 rf.source
  set sdt := sortDrules p rf.target
  set sds := sortDrules p rf.source
  rcases hnt : (sds.nbForced : ℤ) - sdt.nbForced + b with nt | nt
  · rw [hnt] at h
    have hle := checkDbound2Rec_le hredp _ nt sdt.straddling sds.straddling [] p x
      (by simp [dbound1]) hfit h
    rw [dbound2, hsortt, hsorts]
    rw [Int.ofNat_eq_natCast] at hnt
    push_cast
    omega
  · rw [hnt] at h
    simp at h

end Hypermap

/-! ### Bounding the sum of the net transfers across two edges -/

/-- One side of the dual bound check: the part a dart is assumed to fit, the
target rules still to be considered, the source rules, and the target rules
already assumed not to match. -/
structure DSide where
  /-- The part the dart is assumed to fit. -/
  part : Part
  /-- The target rules still to be considered. -/
  target : List Part
  /-- The source rules. -/
  source : List Part
  /-- The target rules already assumed not to match. -/
  excluded : List Part

/-- A side specialised to a part that refines it. -/
def DSide.refine (s : DSide) (q : Part) : DSide :=
  ⟨q, (sortDrules q s.target).straddling, (sortDrules q s.source).straddling, s.excluded⟩

/-- The recursion behind `check2Dbound2`.  The two sides are examined in turn:
when the first has no target rule left, the sides are swapped and the offset
between the two darts is complemented. -/
def check2Dbound2Rec (nhub : ℕ) (redp : Part → Bool) :
    ℕ → DSide → DSide → ℕ → ℕ → Bool
  | 0, _, _, _, _ => false
  | m + 1, s₁, s₂, i, nt =>
      match s₁.target with
      | [] =>
          match s₂.target with
          | [] => true
          | _ :: _ => check2Dbound2Rec nhub redp m s₂ s₁ (nhub - i) nt
      | r :: rt₁ =>
          if rt₁.length + s₂.target.length < nt then true
          else
            (match pruneUnfit (s₁.part.meet r) s₁.excluded with
              | none => true
              | some e₁ =>
                match pruneUnfit ((s₁.part.meet r).rot i) s₂.excluded with
                | none => true
                | some e₂ =>
                  match (sortDrules (s₁.part.meet r) s₁.source).nbForced
                      + ((sortDrules ((s₁.part.meet r).rot i) s₂.source).nbForced + nt)
                      - ((sortDrules (s₁.part.meet r) rt₁).nbForced
                        + (sortDrules ((s₁.part.meet r).rot i) s₂.target).nbForced) with
                  | 0 => redp (s₁.part.meet r)
                  | nt' + 1 =>
                      check2Dbound2Rec nhub redp m
                        (DSide.refine ⟨s₁.part, rt₁, s₁.source, e₁⟩ (s₁.part.meet r))
                        (DSide.refine ⟨s₂.part, s₂.target, s₂.source, e₂⟩
                          ((s₁.part.meet r).rot i)) i nt') &&
            check2Dbound2Rec nhub redp m ⟨s₁.part, rt₁, s₁.source, r :: s₁.excluded⟩ s₂ i nt

/-- The sum of the net charges transferred to a dart fitting `p` exactly and to
the dart `i` faces along is at most `b`. -/
def check2Dbound2 {conv : Part → PRange × Part} {nhub : ℕ} (redp : Part → Bool)
    (rf : DruleFork conv nhub) (p : Part) (i : ℕ) (b : ℤ) : Bool :=
  match ((sortDrules p rf.source).nbForced + (sortDrules (p.rot i) rf.source).nbForced : ℤ)
      - ((sortDrules p rf.target).nbForced + (sortDrules (p.rot i) rf.target).nbForced) + b with
  | .ofNat nt =>
      check2Dbound2Rec nhub redp
        ((sortDrules p rf.target).straddling.length
          + ((sortDrules (p.rot i) rf.target).straddling.length + 3))
        (DSide.refine ⟨p, rf.target, rf.source, []⟩ p)
        (DSide.refine ⟨p.rot i, rf.target, rf.source, []⟩ (p.rot i)) i nt
  | .negSucc _ => false

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {redp : Part → Bool}

/-- Soundness of the recursion behind `check2Dbound2`. -/
theorem check2Dbound2Rec_le {nhub : ℕ}
    (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q) :
    ∀ (m nt i : ℕ) (s₁ s₂ : DSide) (x : D), G.arity x = nhub → i ≤ nhub →
      G.dbound1 s₁.excluded x = 0 → G.ExactFitp x s₁.part →
      G.dbound1 s₂.excluded (G.face^[i] x) = 0 → G.ExactFitp (G.face^[i] x) s₂.part →
      check2Dbound2Rec nhub redp m s₁ s₂ i nt = true →
      G.dbound1 s₁.target x + G.dbound1 s₂.target (G.face^[i] x)
        ≤ nt + (G.dbound1 s₁.source x + G.dbound1 s₂.source (G.face^[i] x)) := by
  intro m
  induction m with
  | zero => intro nt i s₁ s₂ x _ _ _ _ _ _ h; simp [check2Dbound2Rec] at h
  | succ m ih =>
    intro nt i s₁ s₂ x hx hi hru₁ hp₁ hru₂ hp₂ h
    rw [check2Dbound2Rec] at h
    -- the two darts the check is about
    set x₂ := G.face^[i] x with hx₂
    rcases hT₁ : s₁.target with _ | ⟨r, rt₁⟩
    · simp only [hT₁] at h
      rcases hT₂ : s₂.target with _ | ⟨r₂, rt₂⟩
      · simp [dbound1]
      · -- swap the two sides
        simp only [hT₂] at h
        have hx₂n : G.arity x₂ = nhub := by rw [hx₂, G.arity_iterate_face, hx]
        have hback : G.face^[nhub - i] x₂ = x := by
          rw [hx₂, ← Function.iterate_add_apply, Nat.sub_add_cancel hi, ← hx,
            G.iterate_face_arity]
        have hswap := ih nt (nhub - i) s₂ s₁ x₂ hx₂n (Nat.sub_le _ _) hru₂ hp₂
          (by rw [hback]; exact hru₁) (by rw [hback]; exact hp₁) h
        rw [hback, hT₁, hT₂] at hswap
        omega
    · simp only [hT₁] at h
      split at h
      next hlt =>
        have h₁ := G.dbound1_le_length (r :: rt₁) x
        have h₂ := G.dbound1_le_length s₂.target x₂
        simp only [List.length_cons] at h₁
        omega
      next hlt =>
        rw [Bool.and_eq_true] at h
        obtain ⟨hA, hB⟩ := h
        by_cases hr : G.Fitp x r
        · -- the rule applies: refine both sides
          have hq₁ : G.ExactFitp x (s₁.part.meet r) := exactFitp_meet hp₁ hr
          have hsize : i ≤ (s₁.part.meet r).size := by
            rw [Part.size_meet, ← hp₁.1, hx]
            exact hi
          have hq₂ : G.ExactFitp x₂ ((s₁.part.meet r).rot i) :=
            (G.exact_fitp_rot hsize x).mp hq₁
          obtain ⟨e₁, hpr₁, he₁⟩ := pruneUnfit_eq_some hq₁.2 _ hru₁
          obtain ⟨e₂, hpr₂, he₂⟩ := pruneUnfit_eq_some hq₂.2 _ hru₂
          rw [hpr₁, hpr₂] at hA
          have hsT₁ := G.sort_dbound1_eq hq₁.2 rt₁
          have hsS₁ := G.sort_dbound1_eq hq₁.2 s₁.source
          have hsT₂ := G.sort_dbound1_eq hq₂.2 s₂.target
          have hsS₂ := G.sort_dbound1_eq hq₂.2 s₂.source
          rcases hd : (sortDrules (s₁.part.meet r) s₁.source).nbForced
              + ((sortDrules ((s₁.part.meet r).rot i) s₂.source).nbForced + nt)
              - ((sortDrules (s₁.part.meet r) rt₁).nbForced
                + (sortDrules ((s₁.part.meet r).rot i) s₂.target).nbForced) with _ | nt'
          · rw [hd] at hA
            exact absurd hq₁ (hredp x _ hA)
          · rw [hd] at hA
            have hrec := ih nt' i
              (DSide.refine ⟨s₁.part, rt₁, s₁.source, e₁⟩ (s₁.part.meet r))
              (DSide.refine ⟨s₂.part, s₂.target, s₂.source, e₂⟩ ((s₁.part.meet r).rot i))
              x hx hi he₁ hq₁ he₂ hq₂ hA
            simp only [DSide.refine] at hrec
            rw [← hx₂] at hrec
            rw [G.dbound1_cons_pos hr]
            omega
        · rw [G.dbound1_cons_neg hr]
          have hrec := ih nt i ⟨s₁.part, rt₁, s₁.source, r :: s₁.excluded⟩ s₂ x hx hi
            (by simpa using (G.dbound1_cons_neg hr s₁.excluded).trans hru₁) hp₁ hru₂ hp₂ hB
          simp only at hrec
          rw [← hx₂] at hrec
          exact hrec

/-- The sum of the net charges transferred to a dart fitting `p` exactly and to
the dart `i` faces along is at most `b`. -/
theorem check2Dbound2_le {conv : Part → PRange × Part} {nhub : ℕ} {rf : DruleFork conv nhub}
    (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q) {x : D} {p : Part}
    {i : ℕ} {b : ℤ} (hx : G.arity x = nhub) (hfit : G.ExactFitp x p) (hi : i ≤ nhub)
    (h : check2Dbound2 redp rf p i b = true) :
    G.dbound2 rf.target rf.source x + G.dbound2 rf.target rf.source (G.face^[i] x) ≤ b := by
  have hsize : i ≤ p.size := by rw [← hfit.1, hx]; exact hi
  have hfit₂ : G.ExactFitp (G.face^[i] x) (p.rot i) := (G.exact_fitp_rot hsize x).mp hfit
  have hsT₁ := G.sort_dbound1_eq hfit.2 rf.target
  have hsS₁ := G.sort_dbound1_eq hfit.2 rf.source
  have hsT₂ := G.sort_dbound1_eq hfit₂.2 rf.target
  have hsS₂ := G.sort_dbound1_eq hfit₂.2 rf.source
  rw [check2Dbound2] at h
  rcases hnt : ((sortDrules p rf.source).nbForced
      + (sortDrules (p.rot i) rf.source).nbForced : ℤ)
      - ((sortDrules p rf.target).nbForced + (sortDrules (p.rot i) rf.target).nbForced)
      + b with nt | nt
  · rw [hnt] at h
    have hrec := check2Dbound2Rec_le hredp _ nt i
      (DSide.refine ⟨p, rf.target, rf.source, []⟩ p)
      (DSide.refine ⟨p.rot i, rf.target, rf.source, []⟩ (p.rot i)) x hx hi
      (by simp [DSide.refine, dbound1]) (by simpa [DSide.refine] using hfit)
      (by simp [DSide.refine, dbound1]) (by simpa [DSide.refine] using hfit₂) h
    simp only [DSide.refine] at hrec
    rw [dbound2, dbound2]
    rw [Int.ofNat_eq_natCast] at hnt
    omega
  · rw [hnt] at h
    simp at h

end Hypermap

/-! ### Covering the hub

A hubcap is only useful if its constraints cover every edge around the hub, and
if the bounds they impose add up to at most the hub's initial charge.  The
cover is checked by tallying how often each index occurs.
-/

/-- Increment the `i`-th entry of a tally, extending it with zeros if needed. -/
def incrNth : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], i + 1 => 0 :: incrNth [] i
  | n :: v, 0 => (n + 1) :: v
  | n :: v, i + 1 => n :: incrNth v i

/-- Incrementing changes exactly the entry it names. -/
@[simp] theorem getD_incrNth : ∀ (v : List ℕ) (i j : ℕ),
    (incrNth v i).getD j 0 = v.getD j 0 + (if i = j then 1 else 0)
  | [], 0, 0 => rfl
  | [], 0, _ + 1 => by simp [incrNth]
  | [], i + 1, 0 => by simp [incrNth]
  | [], i + 1, j + 1 => by simpa [incrNth] using getD_incrNth [] i j
  | _ :: _, 0, 0 => by simp [incrNth]
  | _ :: _, 0, _ + 1 => by simp [incrNth]
  | _ :: _, i + 1, 0 => by simp [incrNth]
  | n :: v, i + 1, j + 1 => by simpa [incrNth] using getD_incrNth v i j

/-- How often each index occurs in a hubcap. -/
def tallyHubcap : Hubcap → List ℕ
  | .nil => []
  | .one i _ hc => incrNth (tallyHubcap hc) i
  | .two i j _ hc => incrNth (incrNth (tallyHubcap hc) i) j

/-- The recursion behind `hubcapCover`: `b` is the charge still available, and
each constraint is charged once for a uniquely covered index and twice for one
covered by two dual constraints. -/
def hubcapCoverRec (v : List ℕ) : ℤ → Hubcap → Bool
  | b, .nil => !decide (0 < b)
  | b, .one i b' hc => (v.getD i 0 == 1) && hubcapCoverRec v (2 * b' + b) hc
  | b, .two i j b' hc =>
      (v.getD i 0 == v.getD j 0) && decide (v.getD i 0 ≤ 2) &&
        hubcapCoverRec v ((if v.getD i 0 = 1 then 2 else 1) * b' + b) hc

/-- The hubcap covers every index below `nhub`, uniquely except for pairs of
dual constraints, and its bounds leave the hub with a non-positive charge. -/
def hubcapCover (nhub : ℕ) (hc : Hubcap) : Bool :=
  (tallyHubcap hc).length == nhub && !(tallyHubcap hc).contains 0 &&
    hubcapCoverRec (tallyHubcap hc) (2 * dboundK nhub - 1) hc

/-! ### Rotating a part to a constraint -/

/-- The rotation that aligns a part of size `nhub` with the rules at index
`j`: a rotation by `j - 2` modulo `nhub`. -/
def hubRotIdx (nhub j : ℕ) : ℕ := if 2 ≤ j then j - 2 else nhub + j - 2

/-- The part rotated to the constraint at index `j`. -/
def hubcapRot (nhub j : ℕ) (p : Part) : Part := p.rot (hubRotIdx nhub j)

/-- `i - j` modulo `nhub`. -/
def hubSubn (nhub i j : ℕ) : ℕ := (if j ≤ i then i else i + nhub) - j

/-- Every constraint of the hubcap holds for a dart fitting `p`. -/
def hubcapFit {conv : Part → PRange × Part} {nhub : ℕ} (redp : Part → Bool)
    (rf : DruleFork conv nhub) (p : Part) : Hubcap → Bool
  | .nil => true
  | .one j b hc => checkDbound2 redp rf (hubcapRot nhub j p) b && hubcapFit redp rf p hc
  | .two j₁ j₂ b hc =>
      check2Dbound2 redp rf (hubcapRot nhub j₁ p) (hubSubn nhub j₂ j₁) b &&
        hubcapFit redp rf p hc

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D}

/-- Modular arithmetic for the offset between two constraints. -/
theorem hubSubn_le {nhub i j : ℕ} (hi : i < nhub) : hubSubn nhub i j ≤ nhub := by
  rw [hubSubn]
  split <;> omega

omit [Finite D] in
/-- The offset between two constraints, read on the map. -/
theorem iterate_hubSubn {nhub i j : ℕ} (hj : j < nhub) (x : D) (hx : G.arity x = nhub) :
    G.face^[hubSubn nhub i j] (G.face^[j] x) = G.face^[i] x := by
  rw [← Function.iterate_add_apply, hubSubn]
  split
  · rename_i hji
    rw [Nat.sub_add_cancel hji]
  · rename_i hji
    rw [Nat.sub_add_cancel (by omega), Function.iterate_add_apply, ← hx, G.iterate_face_arity]

/-- Rotating the hub dart back by two faces and forward by `j` is a rotation by
`j - 2` modulo `nhub`. -/
theorem iterate_face_invFace2 {nhub j : ℕ} {x : D} (hx : G.arity x = nhub) (h2 : 2 ≤ nhub) :
    G.face^[j] (G.invFace2 x) = G.face^[hubRotIdx nhub j] x := by
  have hinv : G.invFace2 x = G.face^[nhub - 2] x := by
    rw [invFace2_eq_iterate G x (by omega), hx]
  rw [hinv, ← Function.iterate_add_apply, hubRotIdx]
  split
  · rename_i h
    rw [show j + (nhub - 2) = (j - 2) + nhub by omega, Function.iterate_add_apply, ← hx,
      G.iterate_face_arity]
  · rename_i h
    congr 1
    omega

/-- A rotation index stays inside the hub. -/
theorem hubRotIdx_le {nhub j : ℕ} (h2 : 2 ≤ nhub) (hj : j < nhub) : hubRotIdx nhub j ≤ nhub := by
  rw [hubRotIdx]; split <;> omega

/-- The part rotated to the constraint at index `j` fits at the dart the
constraint is about. -/
theorem exactFitp_hubcapRot {nhub j : ℕ} {x : D} {p : Part} (hx : G.arity x = nhub)
    (h2 : 2 ≤ nhub) (hj : j < nhub) (hfit : G.ExactFitp x p) :
    G.ExactFitp (G.face^[j] (G.invFace2 x)) (hubcapRot nhub j p) := by
  rw [iterate_face_invFace2 hx h2, hubcapRot]
  exact (G.exact_fitp_rot (by rw [← hfit.1, hx]; exact hubRotIdx_le h2 hj) x).mp hfit

end Hypermap

/-! ### The weighted total transfer -/

/-- The weight a partial tally `wi` gives to an index whose total tally is
`vi`: an index still to be accounted for carries no weight, one accounted for
twice carries the full weight two, and one accounted for once carries two if it
is uniquely covered and one if it is covered by two dual constraints. -/
def hubWeight (wi vi : ℕ) : ℕ :=
  if 1 < wi then 2 else if wi = 0 then 0 else if vi = 1 then 2 else 1

namespace Hypermap

variable {D : Type*} [Finite D] (G : Hypermap D)

/-- The total charge transfer around the hub of `x`, weighted by a partial
tally `w` against the full tally `v`. -/
noncomputable def sumDb2 (rt rs : List Part) (nhub : ℕ) (v w : List ℕ) (x : D) : ℤ :=
  ∑ i ∈ Finset.range nhub,
    (hubWeight (w.getD i 0) (v.getD i 0) : ℤ) * G.dbound2 rt rs (G.face^[i] x)

variable {G}

omit [Finite D] in
/-- Accounting for one more occurrence of an index adds its transfer, doubled
if the index is uniquely covered. -/
theorem sumDb2_incrNth {rt rs : List Part} {nhub i : ℕ} {v w : List ℕ} {x : D}
    (hi : i < nhub) (hle : w.getD i 0 + 1 ≤ v.getD i 0) (hv2 : v.getD i 0 ≤ 2) :
    G.sumDb2 rt rs nhub v (incrNth w i) x
      = (if v.getD i 0 = 1 then 2 else 1) * G.dbound2 rt rs (G.face^[i] x)
        + G.sumDb2 rt rs nhub v w x := by
  have key : ∀ k,
      (hubWeight ((incrNth w i).getD k 0) (v.getD k 0) : ℤ) * G.dbound2 rt rs (G.face^[k] x)
        = (hubWeight (w.getD k 0) (v.getD k 0) : ℤ) * G.dbound2 rt rs (G.face^[k] x)
          + (if k = i then
              ((if v.getD i 0 = 1 then 2 else 1) : ℤ) * G.dbound2 rt rs (G.face^[i] x) else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      have hstep : hubWeight (1 + w.getD k 0) (v.getD k 0)
          = hubWeight (w.getD k 0) (v.getD k 0) + (if v.getD k 0 = 1 then 2 else 1) := by
        have h : w.getD k 0 = 0 ∨ (w.getD k 0 = 1 ∧ v.getD k 0 = 2) := by omega
        unfold hubWeight
        split_ifs <;> omega
      have hgetD : (incrNth w k).getD k 0 = 1 + w.getD k 0 := by
        rw [getD_incrNth]; simp [Nat.add_comm]
      rw [hgetD, hstep, show (if k = k then
          ((if v.getD k 0 = 1 then (2:ℤ) else 1)) * G.dbound2 rt rs (G.face^[k] x) else 0)
          = ((if v.getD k 0 = 1 then (2:ℤ) else 1)) * G.dbound2 rt rs (G.face^[k] x) from by simp]
      push_cast
      ring
    · have hik : (if i = k then 1 else 0) = 0 := by
        rw [ite_eq_right]
        intro h
        exact absurd h.symm hk
      have hk0 : (if k = i then
          ((if v.getD i 0 = 1 then (2:ℤ) else 1)) * G.dbound2 rt rs (G.face^[i] x) else 0) = 0 := by
        rw [ite_eq_right]
        intro h
        exact absurd h hk
      rw [hk0, getD_incrNth, hik, Nat.add_zero, add_zero]
  simp only [sumDb2]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range nhub) i]
  simp only [Finset.mem_range, hi, ite_true]
  ring

private theorem sum_map_range (n : ℕ) (g : ℕ → ℤ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

omit [Finite D] in
/-- The sum over a face orbit, read as a sum over the indices of the face. -/
theorem sum_orbitList_face (G : Hypermap D) (x : D) (f : D → ℤ) :
    ((orbitList G.face x).map f).sum = ∑ i ∈ Finset.range (G.arity x), f (G.face^[i] x) := by
  rw [orbitList, List.map_map, arity, ← sum_map_range]
  simp [Function.comp_def, Equiv.Perm.coe_pow]

variable {redp : Part → Bool}

/-- The hubcap check bounds the weighted total transfer around the hub. -/
theorem hubcapCoverRec_le {conv : Part → PRange × Part} {nhub : ℕ} {rf : DruleFork conv nhub}
    (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q)
    {x : D} {p : Part} {v : List ℕ} (hx : G.arity x = nhub) (h2 : 2 ≤ nhub)
    (hfit : G.ExactFitp x p) (hvlen : v.length = nhub) :
    ∀ (hc : Hubcap) (b : ℤ), hubcapCoverRec v b hc = true → hubcapFit redp rf p hc = true →
      (∀ k, (tallyHubcap hc).getD k 0 ≤ v.getD k 0) →
      b ≤ - G.sumDb2 rf.target rf.source nhub v (tallyHubcap hc) (G.invFace2 x) := by
  have hx₁ : G.arity (G.invFace2 x) = nhub := by
    rw [invFace2_eq_iterate G x (by omega), G.arity_iterate_face, hx]
  -- an index outside the hub is never tallied
  have hout : ∀ k, nhub ≤ k → v.getD k 0 = 0 := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  intro hc
  induction hc with
  | nil =>
    intro b hcov _ _
    have hb : ¬ (0 < b) := by simpa [hubcapCoverRec] using hcov
    have hzero : G.sumDb2 rf.target rf.source nhub v (tallyHubcap .nil) (G.invFace2 x) = 0 := by
      simp [sumDb2, tallyHubcap, hubWeight]
    rw [hzero]
    omega
  | one i b' hc ih =>
    intro b hcov hfitc hvb
    rw [hubcapCoverRec, Bool.and_eq_true] at hcov
    rw [hubcapFit, Bool.and_eq_true] at hfitc
    obtain ⟨hvi, hcov⟩ := hcov
    obtain ⟨hb', hfitc⟩ := hfitc
    have hvi1 : v.getD i 0 = 1 := by simpa using hvi
    have hi : i < nhub := by
      by_contra hi
      rw [hout i (by omega)] at hvi1
      omega
    have hvb' : ∀ k, (tallyHubcap hc).getD k 0 ≤ v.getD k 0 := by
      intro k
      have := hvb k
      rw [tallyHubcap, getD_incrNth] at this
      omega
    have hle : (tallyHubcap hc).getD i 0 + 1 ≤ v.getD i 0 := by
      have h := hvb i
      rw [tallyHubcap, getD_incrNth] at h
      simpa using h
    have hstep := G.sumDb2_incrNth (rt := rf.target) (rs := rf.source) (x := G.invFace2 x)
      hi hle (by omega)
    have hd := checkDbound2_le hredp
      (exactFitp_hubcapRot hx h2 hi hfit) hb'
    have hih := ih (2 * b' + b) hcov hfitc hvb'
    rw [tallyHubcap, hstep, hvi1]
    norm_num
    linarith
  | two i j b' hc ih =>
    intro b hcov hfitc hvb
    rw [hubcapCoverRec, Bool.and_eq_true, Bool.and_eq_true] at hcov
    rw [hubcapFit, Bool.and_eq_true] at hfitc
    obtain ⟨⟨hvij, hv2⟩, hcov⟩ := hcov
    obtain ⟨hb', hfitc⟩ := hfitc
    have hvij' : v.getD i 0 = v.getD j 0 := by simpa using hvij
    have hv2' : v.getD i 0 ≤ 2 := by simpa using hv2
    -- both indices are tallied, hence inside the hub
    have hvb1 : ∀ k, (incrNth (tallyHubcap hc) i).getD k 0 ≤ v.getD k 0 := by
      intro k
      have := hvb k
      rw [tallyHubcap, getD_incrNth] at this
      omega
    have hvb' : ∀ k, (tallyHubcap hc).getD k 0 ≤ v.getD k 0 := by
      intro k
      have := hvb1 k
      rw [getD_incrNth] at this
      omega
    have hlei : (tallyHubcap hc).getD i 0 + 1 ≤ v.getD i 0 := by
      have h := hvb1 i
      rw [getD_incrNth] at h
      simpa using h
    have hlej : (incrNth (tallyHubcap hc) i).getD j 0 + 1 ≤ v.getD j 0 := by
      have h := hvb j
      rw [tallyHubcap, getD_incrNth] at h
      simpa using h
    have hi : i < nhub := by
      by_contra hi
      rw [hout i (by omega)] at hlei
      omega
    have hj : j < nhub := by
      by_contra hj
      rw [hout j (by omega)] at hlej
      omega
    have hstepj := G.sumDb2_incrNth (rt := rf.target) (rs := rf.source) (x := G.invFace2 x)
      hj hlej (by omega)
    have hstepi := G.sumDb2_incrNth (rt := rf.target) (rs := rf.source) (x := G.invFace2 x)
      hi hlei hv2'
    -- the two transfers the constraint bounds
    have hd := check2Dbound2_le hredp (x := G.face^[i] (G.invFace2 x))
      (by rw [G.arity_iterate_face, hx₁]) (exactFitp_hubcapRot hx h2 hi hfit)
      (hubSubn_le hj) hb'
    rw [iterate_hubSubn hi (G.invFace2 x) hx₁] at hd
    have hih := ih _ hcov hfitc hvb'
    rw [tallyHubcap, hstepj, hstepi, ← hvij']
    by_cases hv1 : v.getD i 0 = 1
    · rw [hv1] at hih ⊢
      norm_num at hih ⊢
      linarith
    · simp only [hv1, ite_false] at hih ⊢
      linarith

/-- A part that passes a covering hubcap check fits no positively charged
dart: the transfers the hubcap bounds already exhaust the hub's charge. -/
theorem not_exactFitp_of_hubcap {conv : Part → PRange × Part} {nhub : ℕ}
    {rf : DruleFork conv nhub} (hplain : G.Plain) (hconv : G.ConverseSpec conv)
    (hredp : ∀ (y : D) (q : Part), redp q = true → ¬ G.ExactFitp y q)
    {x : D} {p : Part} {hc : Hubcap} (hsize : p.size = nhub) (h2 : 2 ≤ nhub)
    (hpos : 0 < G.dscore x) (hcover : hubcapCover nhub hc = true)
    (hfitc : hubcapFit redp rf p hc = true) : ¬ G.ExactFitp x p := by
  intro hfit
  have hx : G.arity x = nhub := by rw [hfit.1, hsize]
  set v := tallyHubcap hc with hv
  rw [hubcapCover, Bool.and_eq_true, Bool.and_eq_true] at hcover
  obtain ⟨⟨hvlen, hv0⟩, hcov⟩ := hcover
  have hvlen' : v.length = nhub := by simpa using hvlen
  -- every index below the hub size is tallied at least once
  have hvpos : ∀ k, k < nhub → 1 ≤ v.getD k 0 := by
    intro k hk
    have hk' : k < v.length := by omega
    have hmem : v[k] ∈ v := List.getElem_mem hk'
    have hne : v[k] ≠ 0 := by
      intro h0
      rw [h0] at hmem
      have hcontains : v.contains 0 = true := List.contains_iff_mem.mpr hmem
      rw [hcontains] at hv0
      simp at hv0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    omega
  -- the dart the constraints are read from
  have hx₁ : G.arity (G.invFace2 x) = nhub := by
    rw [invFace2_eq_iterate G x (by omega), G.arity_iterate_face, hx]
  have hbound := hubcapCoverRec_le hredp hx h2 hfit hvlen' hc _ hcov hfitc (fun _ => le_rfl)
  -- with the full tally every index carries weight two
  have hfull : G.sumDb2 rf.target rf.source nhub v v (G.invFace2 x)
      = 2 * ∑ i ∈ Finset.range nhub, G.dbound2 rf.target rf.source (G.face^[i] (G.invFace2 x)) := by
    rw [sumDb2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := hvpos k (Finset.mem_range.mp hk)
    have hw : hubWeight (v.getD k 0) (v.getD k 0) = 2 := by
      unfold hubWeight
      split_ifs <;> omega
    rw [hw]
    push_cast
    ring
  -- the discharge bound at the same dart
  have hposx₁ : 0 < G.dscore (G.invFace2 x) := by
    have hcf : G.CFace x (G.invFace2 x) := by
      rw [invFace2_eq_iterate G x (by omega)]
      exact ⟨(G.arity x - 2 : ℕ), by simp [Equiv.Perm.coe_pow]⟩
    rwa [← G.dscore_cface hcf]
  have hcap := G.dscore_cap2 hplain hconv hx₁ hposx₁
  rw [sum_orbitList_face, hx₁] at hcap
  rw [← rf.target_eq, ← rf.source_eq] at hcap
  rw [hfull] at hbound
  omega

end Hypermap

end FourColor

import FourColor.MaskRank
import FourColor.Cert

/-!
# Reducibility from one mask walk

`MaskCert` and `MaskRank` turn a single walk of the chromogram tree into the
descent obligation `kempeCoclosure_of_rank` asks for.  This file closes the
remaining gap: it names the set of traces the masks certify, ranks it, and
assembles the walk, the witness data and the contract cover into `CfReducible`.

The certified set is `Masks.Cert`: the traces `certMask` names.  Its rank is
`Masks.levelOf`, the position of the first rank level of `rps` certifying the
trace and `rps.length` when none does.  Neither is ever computed — the descent
only needs the rank to exist — so both are `noncomputable`, and the generator
is left with obligations about masks alone.

The contract half is a mask descent too: `coveredMask` intersects the colour
masks along a concrete trace and asks whether anything certified survives.
-/

namespace FourColor

namespace Masks

/-! ### The certified set and its rank -/

/-- The traces the certificate holds: those `certMask` names. -/
def Cert (ms : Masks) (certMask : ℕ) (et : List Color) : Prop :=
  ∃ i, i < ms.width ∧ certMask.testBit i = true ∧ ms.traceOf i = et

/-- `et` is certified, by an index the rank mask `e` also names. -/
def AtLevel (ms : Masks) (certMask e : ℕ) (et : List Color) : Prop :=
  ∃ i, i < ms.width ∧ certMask.testBit i = true ∧ e.testBit i = true ∧ ms.traceOf i = et

theorem cert_of_atLevel {ms : Masks} {certMask e : ℕ} {et : List Color}
    (h : ms.AtLevel certMask e et) : ms.Cert certMask et := by
  obtain ⟨i, hi, hc, -, ht⟩ := h
  exact ⟨i, hi, hc, ht⟩

open Classical in
/-- The first rank level of `rps` that certifies `et`, counted from zero, and
`rps.length` when none does. -/
noncomputable def levelOf (ms : Masks) (certMask : ℕ) (et : List Color) :
    RankPairs → ℕ
  | [] => 0
  | (e, _) :: ps => if ms.AtLevel certMask e et then 0 else ms.levelOf certMask et ps + 1

/-- A level occurring in the prefix bounds the rank above. -/
theorem levelOf_le (ms : Masks) (certMask : ℕ) (et : List Color) :
    ∀ (pre : RankPairs) (q : ℕ × ℕ) (post : RankPairs),
      ms.AtLevel certMask q.1 et →
        ms.levelOf certMask et (pre ++ q :: post) ≤ pre.length := by
  intro pre
  induction pre with
  | nil =>
    intro q post h
    obtain ⟨e, l⟩ := q
    simp only [List.nil_append, List.length_nil, levelOf]
    exact le_of_eq (if_pos h)
  | cons hd tl ih =>
    intro q post h
    obtain ⟨e, l⟩ := hd
    simp only [List.cons_append, List.length_cons, levelOf]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (ih q post h)

/-- No level of the prefix certifying `et` bounds the rank below. -/
theorem le_levelOf (ms : Masks) (certMask : ℕ) (et : List Color) :
    ∀ (pre post : RankPairs),
      (∀ q ∈ pre, ¬ ms.AtLevel certMask q.1 et) →
        pre.length ≤ ms.levelOf certMask et (pre ++ post) := by
  intro pre
  induction pre with
  | nil => intro post _; simp
  | cons hd tl ih =>
    intro post h
    obtain ⟨e, l⟩ := hd
    simp only [List.cons_append, List.length_cons, levelOf]
    rw [if_neg (h (e, l) List.mem_cons_self)]
    exact Nat.succ_le_succ (ih post fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ### The descent obligation, discharged -/

/-- **Every certified trace lies in the Kempe co-closure.**

`hwit` is what the generator must arrange, and it mentions no ranks: a witness
named by the level's witness mask is a colouring, or *some* permutation of it is
certified at one of the strictly earlier levels.  The ranks are settled here —
the trace being justified ranks at least `pre.length` because the leaf test
found no earlier level among the traces live there, and the witness ranks below
`pre.length` because it is certified inside `pre`. -/
theorem coclosure_of_walk (ms : Masks) (hc : ms.Consistent) (certMask : ℕ)
    (rps : RankPairs) {P : List Color → Prop}
    (hlw : ∀ e l, (e, l) ∈ rps → ∀ j, l.testBit j = true → j < ms.width)
    (hwit : ∀ (pre : RankPairs) (e l : ℕ) (post : RankPairs),
      rps = pre ++ (e, l) :: post →
      ∀ j, j < ms.width → l.testBit j = true →
        P (ms.traceOf j) ∨
          ∃ g : EdgePerm, ∃ q ∈ pre, ms.AtLevel certMask q.1 ((ms.traceOf j).map g))
    (hwalk : ms.walk (leafTest certMask rps) (List.range ms.len) [] ms.full = true)
    (hfull : ∀ i, i < ms.width → ms.full.testBit i = true) :
    ∀ et, ms.Cert certMask et → KempeCoclosure P et := by
  intro et hcert
  refine kempeCoclosure_of_rank (P := P) (S := ms.Cert certMask)
    (fun e => ms.levelOf certMask e rps) ?_ hcert
  rintro et' ⟨i, hi, hcm, rfl⟩ w hmw
  refine ms.hcert_of_walk hc certMask rps (P := P) (S := ms.Cert certMask)
    (rank := fun e => ms.levelOf certMask e rps) hlw ?_ hwalk hfull i hi hcm w hmw
  clear hmw hcm hi i
  intro pre e l post hsplit i hi hcm hnp j hjw hjl
  rcases hwit pre e l post hsplit j hjw hjl with hgood | ⟨g, q, hq, hat⟩
  · exact Or.inl hgood
  refine Or.inr ⟨g, cert_of_atLevel hat, ?_⟩
  -- the witness ranks inside `pre`
  obtain ⟨pre₁, pre₂, rfl⟩ := List.append_of_mem hq
  have hwlt : ms.levelOf certMask ((ms.traceOf j).map g) rps ≤ pre₁.length := by
    rw [hsplit, List.append_assoc, List.cons_append]
    exact ms.levelOf_le certMask _ pre₁ q _ hat
  -- and the trace being justified ranks at or above the whole of `pre`
  have hilt : (pre₁ ++ q :: pre₂).length ≤ ms.levelOf certMask (ms.traceOf i) rps := by
    rw [hsplit]
    refine ms.le_levelOf certMask _ _ _ ?_
    rintro r hr ⟨i', hi', hcm', hrb, htr'⟩
    exact absurd hrb (by rw [hnp r hr i' hi' hcm' htr']; exact Bool.false_ne_true)
  have : pre₁.length < (pre₁ ++ q :: pre₂).length := by
    simp [Nat.lt_succ_iff]
  omega

/-! ### The contract half

A concrete trace is looked up by intersecting the colour masks along it. -/

/-- `c0` stands for "no colour" and names no mask. -/
def okColour : Color → Bool
  | Color.c0 => false
  | _ => true

theorem ne_c0_of_okColour {c : Color} (h : okColour c = true) :
    c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3 := by
  cases c <;> simp [okColour] at h ⊢

/-- Intersect the colour masks of `ct` over the positions `ps`. -/
def liveFrom (ms : Masks) (ct : List Color) : List ℕ → ℕ → ℕ
  | [],      a => a
  | p :: ps, a => ms.liveFrom ct ps (a &&& ms.colourMask p (ct.getD p Color.c0))

/-- The certified traces equal to `ct`. -/
def liveMask (ms : Masks) (certMask : ℕ) (ct : List Color) : ℕ :=
  certMask &&& ms.liveFrom ct (List.range ms.len) ms.full

/-- Some permutation of `ct` is certified. -/
def coveredMask (ms : Masks) (certMask : ℕ) (ct : List Color) : Bool :=
  ct.length == ms.len &&
    allEdgePerms.any fun g =>
      (ct.map g).all okColour && ms.liveMask certMask (ct.map g) != 0

theorem testBit_liveFrom (ms : Masks) (ct : List Color) {i : ℕ} :
    ∀ (ps : List ℕ) (a : ℕ), (ms.liveFrom ct ps a).testBit i = true →
      a.testBit i = true ∧
        ∀ p ∈ ps, (ms.colourMask p (ct.getD p Color.c0)).testBit i = true := by
  intro ps
  induction ps with
  | nil => intro a h; exact ⟨h, by simp⟩
  | cons p ps ih =>
    intro a h
    obtain ⟨ha, hps⟩ := ih _ h
    rw [Nat.testBit_and] at ha
    refine ⟨(Bool.and_eq_true_iff.mp ha).1, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact (Bool.and_eq_true_iff.mp ha).2
    · exact hps q hq'

/-- **A surviving bit is a certified trace equal to `ct`.** -/
theorem cert_of_coveredMask (ms : Masks) (hc : ms.Consistent) (certMask : ℕ)
    {ct : List Color} (h : ms.coveredMask certMask ct = true) :
    ∃ g : EdgePerm, ms.Cert certMask (ct.map g) := by
  rw [coveredMask, Bool.and_eq_true] at h
  obtain ⟨hlen, hany⟩ := h
  obtain ⟨g, -, hg⟩ := List.any_eq_true.mp hany
  rw [Bool.and_eq_true] at hg
  obtain ⟨hall, hg⟩ := hg
  refine ⟨g, ?_⟩
  have hne : ms.liveMask certMask (ct.map g) ≠ 0 := by simpa using hg
  obtain ⟨i, hi⟩ := exists_testBit_of_ne_zero hne
  rw [liveMask, Nat.testBit_and] at hi
  have hcm : certMask.testBit i = true := (Bool.and_eq_true_iff.mp hi).1
  obtain ⟨hfull, hcols⟩ := ms.testBit_liveFrom (ct.map g) _ _ (Bool.and_eq_true_iff.mp hi).2
  have hiw : i < ms.width := by
    rw [full, Nat.testBit_two_pow_sub_one] at hfull
    simpa using hfull
  refine ⟨i, hiw, hcm, ?_⟩
  have hlen' : (ct.map g).length = ms.len := by
    simpa using (beq_iff_eq.mp hlen)
  refine List.ext_getElem (by simp [hlen']) ?_
  intro p hp hp'
  rw [hlen'] at hp'
  rw [ms.getElem_traceOf i p hp']
  have hctlen : ct.length = ms.len := by simpa using hlen'
  have hmem : (ct.map g).getD p Color.c0 = (ct.map g)[p]'(by rw [hlen']; exact hp') := by
    simp [List.getD, List.getElem?_eq_getElem (hctlen ▸ hp' : p < ct.length)]
  have hok : okColour ((ct.map g)[p]'(by rw [hlen']; exact hp')) = true :=
    List.all_eq_true.mp hall _ (List.getElem_mem _)
  have hcbit := hcols p (List.mem_range.mpr hp')
  rw [hmem] at hcbit
  exact (ms.colourAt_eq_iff hp' hiw hc (ne_c0_of_okColour hok)).mpr hcbit

/-- `full` names every index below the width, so the walk really starts from all
of them. -/
theorem testBit_full (ms : Masks) {i : ℕ} (hi : i < ms.width) :
    ms.full.testBit i = true := by
  rw [full, Nat.testBit_two_pow_sub_one]
  simpa using hi

/-- **Reducibility from one mask walk.**

This is what a generated module proves.  Its obligations are, in order: the
masks are a colouring at each position (`hc`); the witness masks stay inside the
universe (`hlw`); each witness is a colouring or permutes into an earlier rank
level (`hwit`); the walk of the chromogram tree succeeds (`hwalk`); and every
contract trace is certified up to a colour permutation (`hcontract`).  Only the
last two are large computations, and each is a declaration of its own. -/
theorem cfReducible_of_masks {cf : Config} {cct : Ctree}
    (hcc : contractCtree cf = some cct)
    (ms : Masks) (hc : ms.Consistent) (certMask : ℕ) (rps : RankPairs)
    (hlw : ∀ e l, (e, l) ∈ rps → ∀ j, l.testBit j = true → j < ms.width)
    (hwit : ∀ (pre : RankPairs) (e l : ℕ) (post : RankPairs),
      rps = pre ++ (e, l) :: post →
      ∀ j, j < ms.width → l.testBit j = true →
        (cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1) (ms.traceOf j) ∨
          ∃ g : EdgePerm, ∃ q ∈ pre, ms.AtLevel certMask q.1 ((ms.traceOf j).map g))
    (hwalk : ms.walk (leafTest certMask rps) (List.range ms.len) [] ms.full = true)
    (hcontract : Ctree.forallMem (fun v => ms.coveredMask certMask (completeTrace v) &&
        ms.coveredMask certMask ((completeTrace v).map EdgePerm.e132)) [] cct = true) :
    CfReducible cf := by
  have hco := ms.coclosure_of_walk hc certMask rps hlw hwit hwalk
    (fun _ hi => ms.testBit_full hi)
  have hcov2 : ∀ ct : List Color, ms.coveredMask certMask ct = true →
      KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1)) ct := by
    intro ct hct
    obtain ⟨g, hg⟩ := ms.cert_of_coveredMask hc certMask hct
    exact kempeCoclosure_of_map g (hco _ hg)
  refine cfReducible_of_coclosure hcc ?_
  intro es hes
  have hall := Ctree.forallMem_sound _ cct [] (evenize es) hcontract hes
  simp only [List.reverse_nil, List.nil_append, Bool.and_eq_true] at hall
  have hrec : completeTrace es = (completeTrace (evenize es)).map (evenPerm es) := by
    rw [← completeTrace_map, map_evenize_evenPerm]
  rw [hrec]
  cases hev : evenTrace es with
  | false =>
    have hp : evenPerm es = EdgePerm.e132 := by unfold evenPerm; rw [hev]; rfl
    rw [hp]
    exact hcov2 _ hall.2
  | true =>
    have hp : evenPerm es = 1 := by unfold evenPerm; rw [hev]; rfl
    rw [hp, map_one_edgePerm]
    exact hcov2 _ hall.1

/-! ### The witness obligation, checked in bulk

A witness index `j` is justified by a *certified* index `i'` carrying the
permuted trace `(traceOf j).map g`.  Checking that index by index would mean one
wide bit test per position per index, and a bit test on a mask of two hundred
thousand bits is not cheap.  `pairWalk` instead walks the trace trie of the
witnesses once, carrying alongside it the mask of the traces that are the
`g`-image of the branch taken.  At a leaf the two masks describe one trace and
its image, and the check is a single intersection. -/

/-- A colour permutation moves the three real colours among themselves. -/
theorem apply_ne_c0 (g : EdgePerm) {c : Color}
    (h : c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3) :
    g.apply c = Color.c1 ∨ g.apply c = Color.c2 ∨ g.apply c = Color.c3 := by
  rcases h with rfl | rfl | rfl <;> cases g <;> decide

/-- Walk the trie of the traces in `a`, carrying in `b` the traces whose colours
are the `g`-images of the branch taken.  `chk` is asked of `b` at each leaf. -/
def pairWalk (ms : Masks) (g : EdgePerm) (chk : ℕ → Bool) :
    List ℕ → ℕ → ℕ → Bool
  | [],      a, b => a == 0 || chk b
  | p :: ps, a, b =>
      a == 0 ||
        (ms.pairWalk g chk ps (a &&& ms.colourMask p Color.c1)
            (b &&& ms.colourMask p (g.apply Color.c1)) &&
         ms.pairWalk g chk ps (a &&& ms.colourMask p Color.c2)
            (b &&& ms.colourMask p (g.apply Color.c2)) &&
         ms.pairWalk g chk ps (a &&& ms.colourMask p Color.c3)
            (b &&& ms.colourMask p (g.apply Color.c3)))

/-- **What a successful `pairWalk` yields.**  For every trace still live in `a`,
some mask the check accepted holds only `g`-images of it. -/
theorem pairWalk_sound (ms : Masks) (hc : ms.Consistent) (g : EdgePerm)
    (chk : ℕ → Bool) :
    ∀ (ps : List ℕ) (a b : ℕ), (∀ p ∈ ps, p < ms.len) →
      ms.pairWalk g chk ps a b = true →
      ∀ i, i < ms.width → a.testBit i = true →
        ∃ b', chk b' = true ∧ (∀ j, b'.testBit j = true → b.testBit j = true) ∧
          ∀ j, j < ms.width → b'.testBit j = true →
            ∀ p ∈ ps, ms.colourAt p j = g.apply (ms.colourAt p i) := by
  intro ps
  induction ps with
  | nil =>
    intro a b _ h i _ hia
    rw [pairWalk, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h0 | hchk
    · rw [h0] at hia; simp at hia
    · exact ⟨b, hchk, fun _ hj => hj, by intro j _ _ p hp; simp at hp⟩
  | cons p ps ih =>
    intro a b hlen h i hi hia
    have hp : p < ms.len := hlen p List.mem_cons_self
    have hlen' : ∀ q ∈ ps, q < ms.len := fun q hq => hlen q (List.mem_cons_of_mem _ hq)
    rw [pairWalk, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h0 | h
    · rw [h0] at hia; simp at hia
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    -- the branch `i` takes is the colour it has here
    have hcases : ms.colourAt p i = Color.c1 ∨ ms.colourAt p i = Color.c2 ∨
        ms.colourAt p i = Color.c3 := by
      have := ms.colourAt_ne_c0 hp hi hc
      cases hcol : ms.colourAt p i <;> simp_all
    have key : ∀ c : Color, c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3 →
        ms.colourAt p i = c →
        ms.pairWalk g chk ps (a &&& ms.colourMask p c) (b &&& ms.colourMask p (g.apply c)) = true →
        ∃ b', chk b' = true ∧ (∀ j, b'.testBit j = true → b.testBit j = true) ∧
          ∀ j, j < ms.width → b'.testBit j = true →
            ∀ q ∈ p :: ps, ms.colourAt q j = g.apply (ms.colourAt q i) := by
      intro c hc3 hcol hw
      have hbit : (a &&& ms.colourMask p c).testBit i = true := by
        rw [Nat.testBit_and, hia, ((ms.colourAt_eq_iff hp hi hc hc3).mp hcol)]
        rfl
      obtain ⟨b', hchk, hmono, hcols⟩ := ih _ _ hlen' hw i hi hbit
      refine ⟨b', hchk, fun j hj => (Bool.and_eq_true_iff.mp
        (by rw [← Nat.testBit_and]; exact hmono j hj)).1, ?_⟩
      intro j hjw hjb q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · have hjc : (ms.colourMask q (g.apply c)).testBit j = true :=
          (Bool.and_eq_true_iff.mp (by rw [← Nat.testBit_and]; exact hmono j hjb)).2
        rw [hcol]
        exact (ms.colourAt_eq_iff hp hjw hc (apply_ne_c0 g hc3)).mpr hjc
      · exact hcols j hjw hjb q hq'
    rcases hcases with hcol | hcol | hcol
    · exact key Color.c1 (Or.inl rfl) hcol h1
    · exact key Color.c2 (Or.inr (Or.inl rfl)) hcol h2
    · exact key Color.c3 (Or.inr (Or.inr rfl)) hcol h3

/-- **One rank level's witnesses, justified by one `pairWalk`.**  `wit` names the
witness indices whose justification is the permutation `g` and the rank level
`e`; the walk checks that each of their `g`-images really is certified there. -/
theorem atLevel_of_pairWalk (ms : Masks) (hc : ms.Consistent) (g : EdgePerm)
    (certMask e wit : ℕ)
    (h : ms.pairWalk g (fun b => b &&& (certMask &&& e &&& ms.full) != 0)
      (List.range ms.len) wit ms.full = true) :
    ∀ i, i < ms.width → wit.testBit i = true →
      ms.AtLevel certMask e ((ms.traceOf i).map g) := by
  intro i hi hw
  obtain ⟨b', hchk, -, hcols⟩ :=
    ms.pairWalk_sound hc g _ (List.range ms.len) wit ms.full
      (fun p hp => List.mem_range.mp hp) h i hi hw
  have hne : b' &&& (certMask &&& e &&& ms.full) ≠ 0 := by simpa using hchk
  obtain ⟨j, hj⟩ := exists_testBit_of_ne_zero hne
  rw [Nat.testBit_and] at hj
  have hjb : b'.testBit j = true := (Bool.and_eq_true_iff.mp hj).1
  have hrest := (Bool.and_eq_true_iff.mp hj).2
  rw [Nat.testBit_and] at hrest
  have hfullj : ms.full.testBit j = true := (Bool.and_eq_true_iff.mp hrest).2
  have hjw : j < ms.width := by
    rw [full, Nat.testBit_two_pow_sub_one] at hfullj
    simpa using hfullj
  have hce := (Bool.and_eq_true_iff.mp hrest).1
  rw [Nat.testBit_and] at hce
  refine ⟨j, hjw, (Bool.and_eq_true_iff.mp hce).1, (Bool.and_eq_true_iff.mp hce).2, ?_⟩
  have hall := hcols j hjw hjb
  simp only [traceOf, List.map_map, Function.comp_def]
  exact List.map_congr_left fun p hp => hall p hp

/-! ### Assembling the levels

The generator's witness data is one entry per rank level: the level's own mask
and the `(permutation, witness mask)` pairs whose images are certified *at* that
level.  The witness mask `firstRank` consults at a level is then forced — it is
the colourings together with everything justified strictly earlier — so
`buildRank` computes it, and the generator only has to check that the numerals
it emitted for the walk agree.  That keeps every index out of the generated
proofs. -/

/-- One level's witness masks, merged. -/
def orMasks : List (EdgePerm × ℕ) → ℕ
  | []      => 0
  | gm :: ws => gm.2 ||| orMasks ws

theorem mem_of_testBit_orMasks :
    ∀ (ws : List (EdgePerm × ℕ)) {j : ℕ}, (orMasks ws).testBit j = true →
      ∃ gm ∈ ws, gm.2.testBit j = true := by
  intro ws
  induction ws with
  | nil => intro j h; simp [orMasks] at h
  | cons gm ws ih =>
    intro j h
    rw [orMasks, Nat.testBit_or] at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h2
    · exact ⟨gm, List.mem_cons_self, h1⟩
    · obtain ⟨gm', hmem, hb⟩ := ih h2
      exact ⟨gm', List.mem_cons_of_mem _ hmem, hb⟩

/-- The rank levels the walk consults, built from the witness data: level `s`
accepts the colourings and everything justified at a strictly earlier level. -/
def buildRank (acc : ℕ) : List (ℕ × List (EdgePerm × ℕ)) → RankPairs
  | []             => []
  | (e, ws) :: rest => (e, acc) :: buildRank (acc ||| orMasks ws) rest

theorem hwit_of_buildRank_aux (ms : Masks) (certMask : ℕ) {P : List Color → Prop} :
    ∀ (wl : List (ℕ × List (EdgePerm × ℕ))) (acc : ℕ) (done : RankPairs),
      (∀ j, j < ms.width → acc.testBit j = true →
        P (ms.traceOf j) ∨
          ∃ g : EdgePerm, ∃ q ∈ done, ms.AtLevel certMask q.1 ((ms.traceOf j).map g)) →
      (∀ ent ∈ wl, ∀ gm ∈ ent.2, ∀ i, i < ms.width → gm.2.testBit i = true →
        ms.AtLevel certMask ent.1 ((ms.traceOf i).map gm.1)) →
      ∀ (pre : RankPairs) (e l : ℕ) (post : RankPairs),
        buildRank acc wl = pre ++ (e, l) :: post →
        ∀ j, j < ms.width → l.testBit j = true →
          P (ms.traceOf j) ∨
            ∃ g : EdgePerm, ∃ q ∈ done ++ pre,
              ms.AtLevel certMask q.1 ((ms.traceOf j).map g) := by
  intro wl
  induction wl with
  | nil =>
    intro acc done _ _ pre e l post hsplit
    exfalso
    cases pre <;> simp [buildRank] at hsplit
  | cons ent rest ih =>
    obtain ⟨e₀, ws₀⟩ := ent
    intro acc done hacc hw pre e l post hsplit j hjw hjl
    rw [buildRank] at hsplit
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨hpair, -⟩ := hsplit
      obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ hpair
      rcases hacc j hjw hjl with hP | ⟨g, q, hq, hat⟩
      · exact Or.inl hP
      · exact Or.inr ⟨g, q, by simpa using hq, hat⟩
    | cons q pre' =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, hrest⟩ := hsplit
      have hacc' : ∀ j, j < ms.width → (acc ||| orMasks ws₀).testBit j = true →
          P (ms.traceOf j) ∨ ∃ g : EdgePerm, ∃ r ∈ done ++ [(e₀, acc)],
            ms.AtLevel certMask r.1 ((ms.traceOf j).map g) := by
        intro k hkw hk
        rw [Nat.testBit_or] at hk
        rcases Bool.or_eq_true_iff.mp hk with h1 | h2
        · rcases hacc k hkw h1 with hP | ⟨g, r, hr, hat⟩
          · exact Or.inl hP
          · exact Or.inr ⟨g, r, List.mem_append_left _ hr, hat⟩
        · obtain ⟨gm, hgm, hb⟩ := mem_of_testBit_orMasks ws₀ h2
          refine Or.inr ⟨gm.1, (e₀, acc), List.mem_append_right _ List.mem_cons_self, ?_⟩
          exact hw (e₀, ws₀) List.mem_cons_self gm hgm k hkw hb
      have := ih (acc ||| orMasks ws₀) (done ++ [(e₀, acc)]) hacc'
        (fun ent hent => hw ent (List.mem_cons_of_mem _ hent)) pre' e l post hrest j hjw hjl
      rcases this with hP | ⟨g, r, hr, hat⟩
      · exact Or.inl hP
      · refine Or.inr ⟨g, r, ?_, hat⟩
        simpa using hr

/-- **The witness obligation from the generator's level data.** -/
theorem hwit_of_buildRank (ms : Masks) (certMask goodMask : ℕ)
    {P : List Color → Prop} (wl : List (ℕ × List (EdgePerm × ℕ)))
    (hgood : ∀ j, j < ms.width → goodMask.testBit j = true → P (ms.traceOf j))
    (hw : ∀ ent ∈ wl, ∀ gm ∈ ent.2, ∀ i, i < ms.width → gm.2.testBit i = true →
      ms.AtLevel certMask ent.1 ((ms.traceOf i).map gm.1)) :
    ∀ (pre : RankPairs) (e l : ℕ) (post : RankPairs),
      buildRank goodMask wl = pre ++ (e, l) :: post →
      ∀ j, j < ms.width → l.testBit j = true →
        P (ms.traceOf j) ∨
          ∃ g : EdgePerm, ∃ q ∈ pre, ms.AtLevel certMask q.1 ((ms.traceOf j).map g) := by
  intro pre e l post hsplit j hjw hjl
  have := ms.hwit_of_buildRank_aux certMask wl goodMask []
    (fun k hk hb => Or.inl (hgood k hk hb)) hw pre e l post hsplit j hjw hjl
  simpa using this

/-! ### The colourings

The good indices are justified against a *checked* tree of colourings — the same
tree and the same check the earlier certificate scheme used, so the one large
computation that forces `cpcolor` is untouched.  What is new is the walk that
connects that tree to the mask universe: it descends the trie of the good
indices and the tree together, and accumulates the colour sum so that the last
position of the trace is confirmed to complete it. -/

/-- The subtree a colour leads to. -/
def branchOf : Ctree → Color → Ctree
  | .node t₁ _ _, Color.c1 => t₁
  | .node _ t₂ _, Color.c2 => t₂
  | .node _ _ t₃, Color.c3 => t₃
  | _,            _        => .empty

theorem sub_cons_eq (t : Ctree) {c : Color}
    (hc : c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3) (et : List Color) :
    Ctree.sub t (c :: et) = Ctree.sub (branchOf t c) et := by
  cases t <;> rcases hc with rfl | rfl | rfl <;> rfl

/-- Walk the trie of `a` against the tree `t` of checked colourings, summing the
colours as it goes.  At the leaf the tree must still hold something and the
position `last` must carry the sum, which is what makes the trace the completion
of the partial one the tree holds. -/
def goodWalk (ms : Masks) (last : ℕ) : List ℕ → Ctree → Color → ℕ → Bool
  | [],      t, acc, a =>
      a == 0 ||
        (acc != Color.c0 && Ctree.mem t [] && (a &&& ms.colourMask last acc == a))
  | p :: ps, t, acc, a =>
      a == 0 ||
        (ms.goodWalk last ps (branchOf t Color.c1) (acc + Color.c1)
            (a &&& ms.colourMask p Color.c1) &&
         ms.goodWalk last ps (branchOf t Color.c2) (acc + Color.c2)
            (a &&& ms.colourMask p Color.c2) &&
         ms.goodWalk last ps (branchOf t Color.c3) (acc + Color.c3)
            (a &&& ms.colourMask p Color.c3))

theorem goodWalk_sound (ms : Masks) (hc : ms.Consistent) (last : ℕ)
    (hlast : last < ms.len) :
    ∀ (ps : List ℕ) (t : Ctree) (acc : Color) (a : ℕ), (∀ p ∈ ps, p < ms.len) →
      ms.goodWalk last ps t acc a = true →
      ∀ i, i < ms.width → a.testBit i = true →
        Ctree.mem t (ps.map (fun p => ms.colourAt p i)) = true ∧
          acc + (ps.map (fun p => ms.colourAt p i)).sum = ms.colourAt last i := by
  intro ps
  induction ps with
  | nil =>
    intro t acc a _ h i hi hia
    rw [goodWalk, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h0 | h
    · rw [h0] at hia; simp at hia
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hne, hmem⟩, hsub⟩ := h
    refine ⟨by simpa using hmem, ?_⟩
    have : (ms.colourMask last acc).testBit i = true := by
      have := hia
      rw [← hsub, Nat.testBit_and] at this
      exact (Bool.and_eq_true_iff.mp this).2
    have hacc : acc = Color.c1 ∨ acc = Color.c2 ∨ acc = Color.c3 := by
      have : acc ≠ Color.c0 := by simpa using hne
      cases acc <;> simp_all
    simp only [List.map_nil, List.sum_nil, add_zero]
    exact ((ms.colourAt_eq_iff hlast hi hc hacc).mpr this).symm
  | cons p ps ih =>
    intro t acc a hlen h i hi hia
    have hp : p < ms.len := hlen p List.mem_cons_self
    have hlen' : ∀ q ∈ ps, q < ms.len := fun q hq => hlen q (List.mem_cons_of_mem _ hq)
    rw [goodWalk, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h0 | h
    · rw [h0] at hia; simp at hia
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hcases : ms.colourAt p i = Color.c1 ∨ ms.colourAt p i = Color.c2 ∨
        ms.colourAt p i = Color.c3 := by
      have := ms.colourAt_ne_c0 hp hi hc
      cases hcol : ms.colourAt p i <;> simp_all
    have key : ∀ c : Color, c = Color.c1 ∨ c = Color.c2 ∨ c = Color.c3 →
        ms.colourAt p i = c →
        ms.goodWalk last ps (branchOf t c) (acc + c) (a &&& ms.colourMask p c) = true →
        Ctree.mem t ((p :: ps).map (fun q => ms.colourAt q i)) = true ∧
          acc + ((p :: ps).map (fun q => ms.colourAt q i)).sum = ms.colourAt last i := by
      intro c hc3 hcol hw
      have hbit : (a &&& ms.colourMask p c).testBit i = true := by
        rw [Nat.testBit_and, hia, ((ms.colourAt_eq_iff hp hi hc hc3).mp hcol)]
        rfl
      obtain ⟨hmem, hsum⟩ := ih _ _ _ hlen' hw i hi hbit
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, hcol, Ctree.mem, sub_cons_eq t hc3]
        exact hmem
      · rw [List.map_cons, hcol, List.sum_cons, ← add_assoc]
        exact hsum
    rcases hcases with hcol | hcol | hcol
    · exact key Color.c1 (Or.inl rfl) hcol h1
    · exact key Color.c2 (Or.inr (Or.inl rfl)) hcol h2
    · exact key Color.c3 (Or.inr (Or.inr rfl)) hcol h3

/-- **The good indices are colourings.**  `hgt` is the one large computation the
earlier scheme already performed — every trace of the emitted tree really is a
colouring of the configuration — and the walk transfers it to the mask
universe. -/
theorem hgood_of_goodWalk (ms : Masks) (hc : ms.Consistent) {cf : Config}
    {good : Ctree} (hlen : 0 < ms.len)
    (hgt : Ctree.forallMem (fun e => Ctree.mem (cpcolor cf.prog) e) [] good = true)
    (goodMask : ℕ)
    (hwalk : ms.goodWalk (ms.len - 1) (List.range (ms.len - 1)) good Color.c0 goodMask
      = true) :
    ∀ j, j < ms.width → goodMask.testBit j = true →
      (cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1) (ms.traceOf j) := by
  intro j hj hb
  obtain ⟨hmem, hsum⟩ := ms.goodWalk_sound hc (ms.len - 1) (by omega)
    (List.range (ms.len - 1)) good Color.c0 goodMask
    (fun p hp => by have := List.mem_range.mp hp; omega) hwalk j hj hb
  have hcpc : Ctree.mem (cpcolor cf.prog)
      ((List.range (ms.len - 1)).map (fun p => ms.colourAt p j)) = true := by
    simpa using Ctree.forallMem_sound _ good [] _ hgt hmem
  have htr : ms.traceOf j =
      completeTrace ((List.range (ms.len - 1)).map (fun p => ms.colourAt p j)) := by
    rw [completeTrace, traceOf]
    have hl : ms.len = (ms.len - 1) + 1 := by omega
    rw [hl, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [← hsum]
    simp
  rw [htr]
  exact ringTrace_rot_of_mem_cpcolor hcpc

/-! ### The checks a generated module runs -/

/-- At each position the three colour masks cover the universe and are pairwise
disjoint.  Four `Nat` operations a position, so this is cheap however wide the
masks are. -/
def consistentCheck (ms : Masks) : Bool :=
  (List.range ms.len).all fun p =>
    (ms.full &&& (ms.colourMask p Color.c1 ||| ms.colourMask p Color.c2 |||
        ms.colourMask p Color.c3) == ms.full) &&
    (ms.colourMask p Color.c1 &&& ms.colourMask p Color.c2 == 0) &&
    (ms.colourMask p Color.c1 &&& ms.colourMask p Color.c3 == 0) &&
    (ms.colourMask p Color.c2 &&& ms.colourMask p Color.c3 == 0)

private theorem not_both_of_and_zero {x y : ℕ} (h : x &&& y = 0) {i : ℕ}
    (hx : x.testBit i = true) (hy : y.testBit i = true) : False := by
  have : (x &&& y).testBit i = true := by rw [Nat.testBit_and, hx, hy]; rfl
  rw [h] at this
  simp at this

theorem consistent_of_check (ms : Masks) (h : ms.consistentCheck = true) :
    ms.Consistent := by
  intro p hp
  have hp' := (List.all_eq_true.mp h) p (List.mem_range.mpr hp)
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp'
  obtain ⟨⟨⟨hcov, h12⟩, h13⟩, h23⟩ := hp'
  rw [beq_iff_eq] at hcov h12 h13 h23
  refine ⟨?_, ?_⟩
  · intro i hi
    have hb : (ms.full &&& (ms.colourMask p Color.c1 ||| ms.colourMask p Color.c2 |||
        ms.colourMask p Color.c3)).testBit i = true := by
      rw [hcov]; exact ms.testBit_full hi
    rw [Nat.testBit_and] at hb
    have hor := (Bool.and_eq_true_iff.mp hb).2
    rw [Nat.testBit_or, Nat.testBit_or] at hor
    rcases Bool.or_eq_true_iff.mp hor with h' | h3
    · rcases Bool.or_eq_true_iff.mp h' with h1 | h2
      · exact ⟨Color.c1, Or.inl rfl, h1⟩
      · exact ⟨Color.c2, Or.inr (Or.inl rfl), h2⟩
    · exact ⟨Color.c3, Or.inr (Or.inr rfl), h3⟩
  · intro i c c' hb hb' hc3 hc3'
    rcases hc3 with rfl | rfl | rfl <;> rcases hc3' with rfl | rfl | rfl <;>
      first
        | rfl
        | exact absurd (not_both_of_and_zero h12 hb hb') (by simp)
        | exact absurd (not_both_of_and_zero h13 hb hb') (by simp)
        | exact absurd (not_both_of_and_zero h23 hb hb') (by simp)
        | exact absurd (not_both_of_and_zero h12 hb' hb) (by simp)
        | exact absurd (not_both_of_and_zero h13 hb' hb) (by simp)
        | exact absurd (not_both_of_and_zero h23 hb' hb) (by simp)

theorem hlw_of_check (ms : Masks) (rps : RankPairs)
    (h : rps.all (fun q => q.2 &&& ms.full == q.2) = true) :
    ∀ e l, (e, l) ∈ rps → ∀ j, l.testBit j = true → j < ms.width := by
  intro e l hmem j hj
  have hq := (List.all_eq_true.mp h) (e, l) hmem
  rw [beq_iff_eq] at hq
  have : (l &&& ms.full).testBit j = true := by rw [hq]; exact hj
  rw [Nat.testBit_and] at this
  have hf := (Bool.and_eq_true_iff.mp this).2
  rw [full, Nat.testBit_two_pow_sub_one] at hf
  simpa using hf

/-- **Reducibility of one configuration from its mask data.**

This is the single theorem a generated module applies.  Of its hypotheses only
three are large computations — the colouring tree `hgt`, the chromogram walk
`hwalk`, and the contract cover `hcontract` — and each is meant to be a
declaration of its own, since the kernel releases a computation's memory when
its declaration ends. -/
theorem cfReducible_of_maskData {cf : Config} {cct good : Ctree}
    (hcc : contractCtree cf = some cct)
    (ms : Masks) (hlen : 0 < ms.len) (hchk : ms.consistentCheck = true)
    (certMask goodMask : ℕ) (wl : List (ℕ × List (EdgePerm × ℕ)))
    (rps : RankPairs) (hrps : rps = buildRank goodMask wl)
    (hgt : Ctree.forallMem (fun e => Ctree.mem (cpcolor cf.prog) e) [] good = true)
    (hgw : ms.goodWalk (ms.len - 1) (List.range (ms.len - 1)) good Color.c0 goodMask = true)
    (hpw : ∀ ent ∈ wl, ∀ gm ∈ ent.2,
      ms.pairWalk gm.1 (fun b => b &&& (certMask &&& ent.1 &&& ms.full) != 0)
        (List.range ms.len) gm.2 ms.full = true)
    (hlwchk : rps.all (fun q => q.2 &&& ms.full == q.2) = true)
    (hwalk : ms.walk (leafTest certMask rps) (List.range ms.len) [] ms.full = true)
    (hcontract : Ctree.forallMem (fun v => ms.coveredMask certMask (completeTrace v) &&
        ms.coveredMask certMask ((completeTrace v).map EdgePerm.e132)) [] cct = true) :
    CfReducible cf := by
  have hc : ms.Consistent := ms.consistent_of_check hchk
  refine ms.cfReducible_of_masks hcc hc certMask rps (ms.hlw_of_check rps hlwchk) ?_
    hwalk hcontract
  subst hrps
  exact ms.hwit_of_buildRank certMask goodMask wl
    (ms.hgood_of_goodWalk hc hlen hgt goodMask hgw)
    (fun ent hent gm hgm i hi hb =>
      ms.atLevel_of_pairWalk hc gm.1 certMask ent.1 gm.2 (hpw ent hent gm hgm) i hi hb)

/-- The colour a mask row is indexed by, so a generated module can give its
masks as an array. -/
def colourCode : Color → ℕ
  | Color.c0 => 0
  | Color.c1 => 1
  | Color.c2 => 2
  | Color.c3 => 3

/-- The contract half as one decidable check. -/
def checkContractMask (ms : Masks) (certMask : ℕ) (cf : Config) : Bool :=
  match contractCtree cf with
  | none => false
  | some cct =>
      Ctree.forallMem (fun v => ms.coveredMask certMask (completeTrace v) &&
        ms.coveredMask certMask ((completeTrace v).map EdgePerm.e132)) [] cct

/-- **Reducibility of one configuration, as a generated module states it.** -/
theorem cfReducible_of_checks {cf : Config} {good : Ctree}
    (ms : Masks) (hlen : 0 < ms.len) (hchk : ms.consistentCheck = true)
    (certMask goodMask : ℕ) (wl : List (ℕ × List (EdgePerm × ℕ)))
    (rps : RankPairs) (hrps : rps = buildRank goodMask wl)
    (hgt : Ctree.forallMem (fun e => Ctree.mem (cpcolor cf.prog) e) [] good = true)
    (hgw : ms.goodWalk (ms.len - 1) (List.range (ms.len - 1)) good Color.c0 goodMask = true)
    (hpw : ∀ ent ∈ wl, ∀ gm ∈ ent.2,
      ms.pairWalk gm.1 (fun b => b &&& (certMask &&& ent.1 &&& ms.full) != 0)
        (List.range ms.len) gm.2 ms.full = true)
    (hlwchk : rps.all (fun q => q.2 &&& ms.full == q.2) = true)
    (hwalk : ms.walk (leafTest certMask rps) (List.range ms.len) [] ms.full = true)
    (hcm : ms.checkContractMask certMask cf = true) :
    CfReducible cf := by
  rw [checkContractMask] at hcm
  cases hcc : contractCtree cf with
  | none => rw [hcc] at hcm; exact absurd hcm (by simp)
  | some cct =>
    rw [hcc] at hcm
    exact ms.cfReducible_of_maskData hcc hlen hchk certMask goodMask wl rps hrps hgt hgw
      hpw hlwchk hwalk hcm

end Masks

end FourColor

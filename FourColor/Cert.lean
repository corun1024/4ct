import FourColor.CertBase

/-!
# The reducibility certificate checker

`checkReducible` of `FourColor.CfReducible` decides C-reducibility by computing
the Kempe closure tree: the greatest Kempe-closed set of ring traces disjoint
from the colourings of the configuration, obtained as a global fixpoint over the
whole trace space.  The check only ever asks that the contract traces lie
*outside* that set, and lying outside it is a least-fixpoint statement with
short local derivations — so the fixpoint need not be computed at all, only a
derivation checked.

A **certificate** is a trace-indexed tree.  Each of its leaves carries

* the trace's **rank**, which strictly decreases along the derivation, and
* a list of **answers**: traces that are either colourings of the configuration
  or, after a colour permutation, members of the certificate of smaller rank.

The leaf is accepted when every chromogram matching its trace is matched by one
of the answers (`coversRec`), and every answer is justified (`checkAnswer`).
The whole certificate is accepted when every leaf is accepted and every trace of
the contract tree is covered.

## Main definitions

* `CTree`, `CTree.find` — certificates and their lookup.
* `coversRec` — every chromogram matching a trace is matched by an answer.
* `checkCert` — the decidable check.

## Main results

* `coversRec_sound` — the specification of `coversRec`.
* `checkCert_sound` — **a configuration with a valid certificate is
  C-reducible.**
-/

namespace FourColor

open Color

/-! ### Certificates -/

/-- Why an answer is already known to lie in the Kempe co-closure: it is a
colouring of the configuration, or it permutes to a member of the certificate
of strictly smaller rank. -/
inductive Reason where
  /-- The answer is a colouring of the configuration. -/
  | good : Reason
  /-- The answer permutes into the certificate at a smaller rank. -/
  | perm (g : EdgePerm) : Reason
  deriving DecidableEq, Repr, Inhabited

/-- One answer of a certificate leaf.  Every answer is a `c2`/`c3` flip of its
leaf's own trace — that is forced, since the traces matching a chromogram that
the leaf's trace matches are exactly its chord flips — so an answer is a bit
mask over the positions, not a trace.  The witness is the completion of the
flipped partial trace. -/
structure Answer where
  /-- Which positions of the leaf's partial trace to swap `c2` for `c3` at. -/
  mask : ℕ
  /-- Why the witness is justified. -/
  reason : Reason
  deriving Repr, Inhabited

/-- Swap `c2` and `c3` at the positions selected by `m`, counting from `i`. -/
def flipFrom (m : ℕ) (i : ℕ) : List Color → List Color
  | [] => []
  | c :: cs =>
      (if m.testBit i then (match c with | .c2 => .c3 | .c3 => .c2 | x => x) else c)
        :: flipFrom m (i + 1) cs

/-- The partial trace an answer denotes at a leaf whose trace is `u`. -/
def Answer.witnessPart (a : Answer) (u : List Color) : List Color :=
  flipFrom a.mask 0 u.dropLast

/-- A certificate: a ternary trace-indexed tree whose leaves carry a rank and
the answers for that trace. -/
inductive CTree where
  /-- A node with the subtrees for `c1`, `c2` and `c3`. -/
  | node (t₁ t₂ t₃ : CTree) : CTree
  /-- A leaf: the rank of the trace leading here, and its answers. -/
  | leaf (rank : ℕ) (answers : List Answer) : CTree
  /-- The empty certificate. -/
  | empty : CTree
  deriving Inhabited

/-- The leaf data of a certificate at a trace. -/
def CTree.find : CTree → List Color → Option (ℕ × List Answer)
  | .node t₁ t₂ t₃, e :: et =>
      match e with
      | .c0 => none
      | .c1 => t₁.find et
      | .c2 => t₂.find et
      | .c3 => t₃.find et
  | .leaf r ans, [] => some (r, ans)
  | _, _ => none

/-- The traces a certificate justifies. -/
def CTree.Mem (D : CTree) (et : List Color) : Prop := (D.find et).isSome = true

/-- The rank a certificate assigns to a trace; junk outside it. -/
def CTree.rankOf (D : CTree) (et : List Color) : ℕ := ((D.find et).map Prod.fst).getD 0

/-! ### Covering the chromograms of a trace

`coversRec et ess lb` enumerates the chromograms matching `et` in the context
`lb`, carrying the answers along in lockstep; it accepts when every one of them
is matched by some answer.  The answers are carried as pairs of their own open
chord context and their remaining colours, exactly as `matchg` would consume
them. -/

/-- Consume one symbol against an answer. -/
def stepAns (s : GramSymbol) : List Bool × List Color → Option (List Bool × List Color)
  | (_, []) => none
  | (bs, e :: es) =>
      match matchStep e s bs with
      | none => none
      | some bs' => some (bs', es)

/-- One symbol of the enumeration: if the symbol is compatible with the head of
the trace, the answers filtered by it must still cover the rest. -/
def coversStep (rec : List (List Bool × List Color) → List Bool → Bool)
    (e : Color) (ess : List (List Bool × List Color)) (lb : List Bool)
    (s : GramSymbol) : Bool :=
  match matchStep e s lb with
  | none => true
  | some lb' => rec (ess.filterMap (stepAns s)) lb'

/-- Every chromogram matching `et` in the context `lb` is matched by one of the
answers `ess`. -/
def coversRec : List Color → List (List Bool × List Color) → List Bool → Bool
  | [], ess, lb => !lb.isEmpty || ess.any fun p => p.1.isEmpty && p.2.isEmpty
  | e :: et, ess, lb =>
      coversStep (coversRec et) e ess lb .push &&
        coversStep (coversRec et) e ess lb .skip &&
          coversStep (coversRec et) e ess lb .pop0 &&
            coversStep (coversRec et) e ess lb .pop1

/-- **The specification of `coversRec`**: if it accepts, then every chromogram
matching the trace is matched by one of the answers. -/
theorem coversRec_sound : ∀ (et : List Color) (ess : List (List Bool × List Color))
    (lb : List Bool), coversRec et ess lb = true →
      ∀ w, matchg lb et w = true → ∃ p ∈ ess, matchg p.1 p.2 w = true := by
  intro et
  induction et with
  | nil =>
    intro ess lb hcov w hw
    -- only the empty chromogram matches the empty trace, and only with no open chords
    cases w with
    | cons s w => simp [matchg] at hw
    | nil =>
      rw [matchg_nil_nil, List.isEmpty_iff] at hw
      subst hw
      simp only [coversRec, List.isEmpty_nil, Bool.not_true, Bool.false_or,
        List.any_eq_true] at hcov
      obtain ⟨p, hp, hq⟩ := hcov
      rw [Bool.and_eq_true, List.isEmpty_iff, List.isEmpty_iff] at hq
      refine ⟨p, hp, ?_⟩
      rw [hq.1, hq.2, matchg_nil_nil, List.isEmpty_nil]
  | cons e et ih =>
    intro ess lb hcov w hw
    cases w with
    | nil => simp [matchg] at hw
    | cons s w =>
      rw [matchg_cons] at hw
      -- the head symbol must be compatible with the head colour
      cases hstep : matchStep e s lb with
      | none => rw [hstep] at hw; simp at hw
      | some lb' =>
        rw [hstep] at hw
        simp only [Option.elim] at hw
        -- the enumeration covered this symbol
        have hs : coversStep (coversRec et) e ess lb s = true := by
          simp only [coversRec, Bool.and_eq_true] at hcov
          cases s
          · exact hcov.1.1.1
          · exact hcov.1.1.2
          · exact hcov.1.2
          · exact hcov.2
        rw [coversStep, hstep] at hs
        obtain ⟨q, hqmem, hq⟩ := ih _ _ hs w hw
        obtain ⟨p, hpmem, hpq⟩ := List.mem_filterMap.mp hqmem
        refine ⟨p, hpmem, ?_⟩
        obtain ⟨bs, es⟩ := p
        cases es with
        | nil => simp [stepAns] at hpq
        | cons e' es =>
          simp only [stepAns] at hpq
          cases hstep' : matchStep e' s bs with
          | none => rw [hstep'] at hpq; simp at hpq
          | some bs' =>
            rw [hstep'] at hpq
            simp only [Option.some.injEq] at hpq
            subst hpq
            rw [matchg_cons, hstep']
            simpa using hq

/-! ### The checker -/

/-- The six colour permutations. -/
def allEdgePerms : List EdgePerm := [.e123, .e132, .e213, .e231, .e312, .e321]

/-! ### The two oracles

The inner loop of the check is two lookups: "is this partial trace a colouring
of the configuration?" and "is this trace certified, and at what rank?".  Both
are abstracted here, so that the representation of the data can change — a
packed `Nat` read with `Nat.testBit`, say, instead of a tree walk — without
touching the soundness proof.  An oracle only has to be *sound*: whatever it
accepts must really be held by the tree it stands for. -/

/-- An answer is justified: it is a colouring of the configuration, or it
permutes into the certificate at a strictly smaller rank. -/
def checkAnswer (memGood : List Color → Bool) (lookup : List Color → Option ℕ)
    (u : List Color) (r : ℕ) (a : Answer) : Bool :=
  match a.reason with
  | .good => memGood (a.witnessPart u)
  | .perm g =>
      match lookup ((completeTrace (a.witnessPart u)).map g) with
      | none => false
      | some r' => decide (r' < r)

/-- One leaf of the certificate is accepted. -/
def checkLeaf (memGood : List Color → Bool) (lookup : List Color → Option ℕ)
    (u : List Color) (r : ℕ) (ans : List Answer) : Bool :=
  coversRec u (ans.map fun a => ([], completeTrace (a.witnessPart u))) [] &&
    ans.all (checkAnswer memGood lookup u r)

/-- Every leaf of a certificate is accepted; `pre` is the reversed prefix.  The
tree argument is the subtree being walked, so a walk splits into independent
walks of its subtrees — which is how one configuration's check is spread over
several declarations. -/
def checkTree (memGood : List Color → Bool) (lookup : List Color → Option ℕ) :
    List Color → CTree → Bool
  | _, .empty => true
  | pre, .leaf r ans => checkLeaf memGood lookup pre.reverse r ans
  | pre, .node t₁ t₂ t₃ =>
      checkTree memGood lookup (.c1 :: pre) t₁ && checkTree memGood lookup (.c2 :: pre) t₂ &&
        checkTree memGood lookup (.c3 :: pre) t₃

/-- The leaf obligations hold at every trace the certificate holds. -/
theorem checkTree_sound (memGood : List Color → Bool) (lookup : List Color → Option ℕ) :
    ∀ (t : CTree) (pre et : List Color) (r : ℕ) (ans : List Answer),
      checkTree memGood lookup pre t = true → t.find et = some (r, ans) →
      checkLeaf memGood lookup (pre.reverse ++ et) r ans = true := by
  intro t
  induction t with
  | empty => intro pre et r ans _ hfind; cases et <;> simp [CTree.find] at hfind
  | leaf r' ans' =>
    intro pre et r ans hchk hfind
    cases et with
    | cons e et => simp [CTree.find] at hfind
    | nil =>
      simp only [CTree.find, Option.some.injEq, Prod.mk.injEq] at hfind
      obtain ⟨rfl, rfl⟩ := hfind
      simp only [List.append_nil]
      exact hchk
  | node t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    intro pre et r ans hchk hfind
    cases et with
    | nil => simp [CTree.find] at hfind
    | cons e et =>
      simp only [checkTree, Bool.and_eq_true] at hchk
      have hcons : ∀ c : Color, (c :: pre).reverse ++ et = pre.reverse ++ c :: et := by
        intro c; simp
      cases e with
      | c0 => simp [CTree.find] at hfind
      | c1 => rw [← hcons .c1]; exact ih₁ _ _ _ _ hchk.1.1 hfind
      | c2 => rw [← hcons .c2]; exact ih₂ _ _ _ _ hchk.1.2 hfind
      | c3 => rw [← hcons .c3]; exact ih₃ _ _ _ _ hchk.2 hfind

/-- A trace is covered when some colour permutation of it is in the
certificate. -/
def covered (lookup : List Color → Option ℕ) (ct : List Color) : Bool :=
  allEdgePerms.any fun g => (lookup (ct.map g)).isSome

/-- Every trace a colouring tree holds satisfies `p`; `pre` is the reversed
prefix. -/
def Ctree.forallMem (p : List Color → Bool) : List Color → Ctree → Bool
  | _, .empty => true
  | pre, .leaf _ => p pre.reverse
  | pre, .node t₁ t₂ t₃ =>
      Ctree.forallMem p (.c1 :: pre) t₁ && Ctree.forallMem p (.c2 :: pre) t₂ &&
        Ctree.forallMem p (.c3 :: pre) t₃

/-- The specification of `Ctree.forallMem`. -/
theorem Ctree.forallMem_sound (p : List Color → Bool) :
    ∀ (t : Ctree) (pre et : List Color), Ctree.forallMem p pre t = true →
      Ctree.mem t et = true → p (pre.reverse ++ et) = true := by
  intro t
  induction t with
  | empty => intro pre et _ hmem; simp [Ctree.mem, Ctree.sub] at hmem
  | leaf lf _ =>
    intro pre et hall hmem
    cases et with
    | cons e et => simp [Ctree.mem, Ctree.sub] at hmem
    | nil =>
      have h2 : p pre.reverse = true := hall
      simpa using h2
  | node t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    intro pre et hall hmem
    simp only [Ctree.forallMem, Bool.and_eq_true] at hall
    cases et with
    | nil => simp [Ctree.mem, Ctree.sub] at hmem
    | cons e et =>
      cases e with
      | c0 => simp [Ctree.mem, Ctree.sub] at hmem
      | c1 => simpa using ih₁ (Color.c1 :: pre) et hall.1.1 hmem
      | c2 => simpa using ih₂ (Color.c2 :: pre) et hall.1.2 hmem
      | c3 => simpa using ih₃ (Color.c3 :: pre) et hall.2 hmem

/-- **The certificate check.**  The configuration has a well-formed contract,
every leaf of the certificate is accepted, and every trace of the contract tree
is covered — in both of its two even forms. -/
def checkCertWith (memGood : List Color → Bool) (lookup : List Color → Option ℕ)
    (cf : Config) (D : CTree) : Bool :=
  match contractCtree cf with
  | none => false
  | some cct =>
      checkTree memGood lookup [] D &&
        Ctree.forallMem (fun v => covered lookup (completeTrace v) &&
          covered lookup ((completeTrace v).map EdgePerm.e132)) [] cct

/-- The plain lookup: walk the certificate tree. -/
def CTree.lookup (D : CTree) (et : List Color) : Option ℕ := (D.find et).map Prod.fst

/-- The check with the two direct oracles. -/
def checkCert (cf : Config) (D : CTree) : Bool :=
  checkCertWith (Ctree.mem (cpcolor cf.prog)) D.lookup cf D

/-! ### Soundness -/

/-- Completing a partial trace commutes with colour permutations. -/
theorem completeTrace_map (g : EdgePerm) (et : List Color) :
    completeTrace (et.map g) = (completeTrace et).map g := by
  simp [completeTrace, map_sum]

/-- A trace is the image of its even form under the permutation that evened
it. -/
theorem map_evenize_evenPerm (es : List Color) : (evenize es).map (evenPerm es) = es := by
  unfold evenize
  cases h : evenTrace es with
  | false =>
    have hp : evenPerm es = EdgePerm.e132 := by unfold evenPerm; rw [h]; rfl
    rw [hp, List.map_map]
    refine (List.map_congr_left ?_).trans (List.map_id _)
    intro c _
    cases c <;> rfl
  | true =>
    have hp : evenPerm es = 1 := by unfold evenPerm; rw [h]; rfl
    rw [hp, map_one_edgePerm, map_one_edgePerm]

/-- **Soundness of the certificate check**, against any pair of sound oracles.

`memGood` must only accept partial traces the colouring tree really holds, and
`lookup` must only report a rank the certificate tree really carries; both are
one-directional, so a faster representation may under-approximate freely.

This replaces the Kempe closure fixpoint of `checkReducible`: instead of
computing the greatest Kempe-closed set of traces disjoint from the colourings
of the configuration and checking the contract tree against it, the certificate
exhibits, for each contract trace, a finite derivation of its membership in the
Kempe co-closure. -/
theorem checkCertWith_sound {cf : Config} {D : CTree}
    {memGood : List Color → Bool} {lookup : List Color → Option ℕ}
    (hgd : ∀ e, memGood e = true → Ctree.mem (cpcolor cf.prog) e = true)
    (hlk : ∀ et r, lookup et = some r → ∃ ans, D.find et = some (r, ans))
    (h : checkCertWith memGood lookup cf D = true) : CfReducible cf := by
  rw [checkCertWith] at h
  cases hc : contractCtree cf with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some cct =>
    rw [hc, Bool.and_eq_true] at h
    obtain ⟨hleaves, hcontract⟩ := h
    -- a lookup hit is a certified trace of that rank
    have hmemof : ∀ et r, lookup et = some r →
        CTree.Mem D et ∧ D.rankOf et = r := by
      intro et r hr
      obtain ⟨ans, hf⟩ := hlk et r hr
      refine ⟨?_, ?_⟩
      · unfold CTree.Mem
        rw [hf]; rfl
      · unfold CTree.rankOf
        rw [hf]; rfl
    -- every trace the certificate holds lies in the Kempe co-closure
    have hcert : ∀ et, CTree.Mem D et →
        KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1)) et := by
      intro et hmem
      refine @kempeCoclosure_of_rank _ (CTree.Mem D) (CTree.rankOf D) ?_ et hmem
      intro u hu w hw
      obtain ⟨⟨r, ans⟩, hfind⟩ := Option.isSome_iff_exists.mp hu
      have hleaf := checkTree_sound memGood lookup D [] u r ans hleaves hfind
      simp only [List.reverse_nil, List.nil_append, checkLeaf, Bool.and_eq_true] at hleaf
      obtain ⟨hcov, hans⟩ := hleaf
      obtain ⟨p, hp, hpw⟩ := coversRec_sound u _ [] hcov w hw
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      refine ⟨completeTrace (a.witnessPart u), hpw, ?_⟩
      have hcheck : checkAnswer memGood lookup u r a = true :=
        (List.all_eq_true.mp hans) a ha
      rcases hr : a.reason with _ | g
      · simp only [checkAnswer, hr] at hcheck
        exact Or.inl (ringTrace_rot_of_mem_cpcolor (hgd _ hcheck))
      · simp only [checkAnswer, hr] at hcheck
        rcases hf : lookup ((completeTrace (a.witnessPart u)).map g) with _ | r'
        · simp [hf] at hcheck
        · simp only [hf] at hcheck
          obtain ⟨hmem', hrank'⟩ := hmemof _ _ hf
          refine Or.inr ⟨g, hmem', ?_⟩
          rw [hrank', CTree.rankOf, hfind]
          simpa using hcheck
    -- a covered trace lies in the co-closure, by rule (P)
    have hcov2 : ∀ ct : List Color, covered lookup ct = true →
        KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1)) ct := by
      intro ct hct
      obtain ⟨g, -, hg⟩ := List.any_eq_true.mp hct
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hg
      exact kempeCoclosure_of_map g (hcert _ (hmemof _ _ hr).1)
    refine cfReducible_of_coclosure hc ?_
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

/-- **Soundness of the certificate check** with the direct oracles. -/
theorem checkCert_sound {cf : Config} {D : CTree} (h : checkCert cf D = true) :
    CfReducible cf :=
  checkCertWith_sound (fun _ he => he)
    (fun et r hr => by
      simp only [CTree.lookup] at hr
      rcases hf : D.find et with _ | ⟨r', ans'⟩
      · rw [hf] at hr; simp at hr
      · rw [hf] at hr
        have hrr : r' = r := by simpa using hr
        exact ⟨ans', by rw [hrr]⟩)
    h

/-! ### Splitting one configuration's check across declarations

The kernel releases the memory of a computation when its *declaration* ends, so
a check too large to run in one piece is run in several.  Both halves of
`checkCertWith` split: the walk over the certificate splits into the walks of
its subtrees (`checkTree_node`), and the two halves themselves are independent
(`checkCert_of_parts`).  The certificate is emitted with its subtrees as
separate data definitions, so each declaration decodes and walks one part while
the whole certificate remains available for the rank lookups. -/

/-- The contract half of the check: the configuration has a well-formed
contract, and every trace of its contract tree is covered in both of its even
forms. -/
def checkContract (lookup : List Color → Option ℕ) (cf : Config) : Bool :=
  match contractCtree cf with
  | none => false
  | some cct =>
      Ctree.forallMem (fun v => covered lookup (completeTrace v) &&
        covered lookup ((completeTrace v).map EdgePerm.e132)) [] cct

/-- The check is the walk and the contract cover, independently. -/
theorem checkCertWith_eq (memGood : List Color → Bool) (lookup : List Color → Option ℕ)
    (cf : Config) (D : CTree) :
    checkCertWith memGood lookup cf D =
      (checkTree memGood lookup [] D && checkContract lookup cf) := by
  unfold checkCertWith checkContract
  cases contractCtree cf <;> simp

/-- The walk of an empty subtree is trivial. -/
theorem checkTree_empty (memGood : List Color → Bool) (lookup : List Color → Option ℕ)
    (pre : List Color) : checkTree memGood lookup pre .empty = true := rfl

/-- **The walk splits at a node.**  This is what lets one configuration's check
be spread over as many declarations as its size needs: each subtree is walked in
a declaration of its own, and the walks are glued here. -/
theorem checkTree_node {memGood : List Color → Bool} {lookup : List Color → Option ℕ}
    {t₁ t₂ t₃ : CTree} {pre : List Color}
    (h₁ : checkTree memGood lookup (Color.c1 :: pre) t₁ = true)
    (h₂ : checkTree memGood lookup (Color.c2 :: pre) t₂ = true)
    (h₃ : checkTree memGood lookup (Color.c3 :: pre) t₃ = true) :
    checkTree memGood lookup pre (.node t₁ t₂ t₃) = true := by
  simp [checkTree, h₁, h₂, h₃]

/-- **Soundness from the two halves separately**, so that a job module can
discharge them in different declarations. -/
theorem checkCert_of_parts {cf : Config} {D : CTree}
    (hw : checkTree (Ctree.mem (cpcolor cf.prog)) D.lookup [] D = true)
    (hv : checkContract D.lookup cf = true) : CfReducible cf := by
  refine checkCert_sound (D := D) ?_
  rw [checkCert, checkCertWith_eq, hw, hv]
  rfl

/-- **Soundness from the two halves and a checked table of colourings.**

`g` stands for the colourings the certificate's `good` answers appeal to.  `hg`
says every trace it holds really is one, and is the only place the colouring
tree of the configuration is built — which matters, because building that tree
is the largest single kernel computation the development performs. -/
theorem checkCert_of_parts_good {cf : Config} {D : CTree} {g : Ctree}
    (hg : Ctree.forallMem (fun e => Ctree.mem (cpcolor cf.prog) e) [] g = true)
    (hw : checkTree (Ctree.mem g) D.lookup [] D = true)
    (hv : checkContract D.lookup cf = true) : CfReducible cf := by
  refine checkCertWith_sound (D := D) (memGood := Ctree.mem g) (lookup := D.lookup)
    (fun e he => ?_) (fun et r hr => ?_) ?_
  · simpa using Ctree.forallMem_sound _ g [] e hg he
  · simp only [CTree.lookup] at hr
    rcases hf : D.find et with _ | ⟨r', ans'⟩
    · rw [hf] at hr; simp at hr
    · rw [hf] at hr
      have hrr : r' = r := by simpa using hr
      exact ⟨ans', by rw [hrr]⟩
  · rw [checkCertWith_eq, hw, hv]
    rfl

end FourColor

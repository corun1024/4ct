import FourColor.Part
import FourColor.QuizTree

/-!
# Reducibility check for parts

`redpart qzt p0` decides that every 2-neighbourhood matching the part `p0`
contains the embedded kernel of one of the reducible configurations stored in
the quiz tree `qzt`.  The search navigates the part with a *zipper*: a reversed
left sector, a right sector, and an index naming one dart of the second
neighbourhood of the hub.  At each position the top of the arity ranges is
matched against the quizzes stored in the tree, and the check recurses on the
parts obtained by *popping* the ranges that were matched.

Only soundness is proved, as in the reference development: if `redpart` accepts
a part then no dart of a plain cubic pentagonal map whose quiz tree fits
nowhere can fit that part.

## Main definitions

* `ZpartLoc`, `Zpart` — the zipper and the index of the dart it names.
* `Hypermap.zmove`, `Hypermap.zorg`, `Hypermap.zdart` — the dart of a zipper.
* `Zvalid` — the zipper sectors concatenate to two copies of the part.
* `zshiftl`, `zshiftr`, `zstepL`, `zstepR` and their `t` variants — zipper
  navigation; the `t` variants assume the arity at the zipper dart is the top
  of its range, which lets them handle the doubled quiz steps.
* `zrange`, `topqa`, `Fitqa`, `popqa` — the arity range the part imposes at the
  zipper dart, its top value, and the range with that top value removed.
* `redPcons`, `redPop` — the recursive check on the parts obtained by popping a
  range.
* `Fitqzp`, `redPopqzp`, `redQztLeaf` — matching a question, then a whole leaf
  list of the quiz tree, against the tops of the ranges of a zipper.
* `redZpartStep`, `redZpartRec`, `redZpart`, `redpart` — the reducibility walk
  around the hub and the check itself.

## Main results

* `Hypermap.zrange_dart` — the zipper dart has the arity the part prescribes.
* `Hypermap.zdart_stepL`, `Hypermap.zdart_stepR` and the `t` variants — the
  zipper steps follow the quiz steps.
* `Hypermap.redPop_fit` — a matched range really pins down the arity.
* `Hypermap.fitqzp_fit` — a question that matches a zipper really fits at the
  zipper dart.
* `Hypermap.no_fit_redpart` — soundness: a part accepted by `redpart` fits no
  dart of a plain cubic pentagonal map whose quiz tree fits nowhere.
-/

namespace FourColor

/-! ### Zipper parts -/

/-- The index of the dart a zipper part names.  `hub*` and `hat*` are the two
node orbits that fall between the left and right sectors; `fan_l` and `fan_r`
are the two chains of quiz steps that run around the left spoke face, numbered
in decreasing order so that the hat dart at the end of each chain is `0`;
`nil` is the out-of-bounds value. -/
inductive ZpartLoc
  | nil
  | hub | hubl | hubr
  | hat | hatl | hatr
  | fan0l | fan1l | fan2l | fan3l
  | fan0r | fan1r | fan2r | fan3r
  deriving DecidableEq, Repr

/-- A zipper part: a reversed left sector, a right sector, and the index of
the dart the zipper names. -/
structure Zpart where
  /-- The index of the dart the zipper names. -/
  loc : ZpartLoc
  /-- The left sector, in reverse order (but *not* mirrored). -/
  left : Part
  /-- The right sector. -/
  right : Part
  deriving DecidableEq, Repr

namespace Zpart

/-- The zipper names an actual dart. -/
def Proper (zp : Zpart) : Prop := zp.loc ≠ .nil

instance (zp : Zpart) : Decidable zp.Proper := by unfold Proper; infer_instance

@[simp] theorem proper_mk (zi : ZpartLoc) (pl pr : Part) :
    (Zpart.mk zi pl pr).Proper ↔ zi ≠ .nil := Iff.rfl

end Zpart

namespace Part

/-- Move the first subpart of `p1` to the front of `p2`; this is the right
shift used to rotate a zipper. -/
def shift (p1 p2 : Part) : Part := (p1.take 1).cat p2

@[simp] theorem shift_nil (p : Part) : shift .nil p = p := rfl

@[simp] theorem shift_cons (s h : PRange) (p q : Part) :
    shift (.cons s h p) q = .cons s h q := rfl

@[simp] theorem shift_cons6 (h f1 : PRange) (p q : Part) :
    shift (.cons6 h f1 p) q = .cons6 h f1 q := rfl

@[simp] theorem shift_cons7 (h f1 f2 : PRange) (p q : Part) :
    shift (.cons7 h f1 f2 p) q = .cons7 h f1 f2 q := rfl

@[simp] theorem shift_cons8 (h f1 f2 f3 : PRange) (p q : Part) :
    shift (.cons8 h f1 f2 f3 p) q = .cons8 h f1 f2 f3 q := rfl

/-- Shifting right does not change the reverse concatenation. -/
theorem catrev_shift_left (pl pr : Part) :
    pl.catrev pr = (pl.drop 1).catrev (shift pl pr) := by
  cases pl <;> rfl

/-- Shifting left does not change the reverse concatenation. -/
theorem catrev_shift_right (pl pr : Part) :
    pl.catrev pr = (shift pr pl).catrev (pr.drop 1) := by
  cases pr <;> rfl

/-- A shifted sector has the size of the sector it is prefixed to, plus one,
unless the shifting sector is empty. -/
theorem size_shift_of_ne_nil {p : Part} (h : p ≠ .nil) (q : Part) :
    (shift p q).size = q.size + 1 := by
  cases p with
  | nil => exact absurd rfl h
  | _ => simp [shift, take, cat, size]

/-- A shifted sector is never empty, unless the shifting sector is. -/
theorem shift_ne_nil {p : Part} (h : p ≠ .nil) (q : Part) : shift p q ≠ .nil := by
  cases p with
  | nil => exact absurd rfl h
  | _ => simp [shift, take, cat]

/-- Dropping one subpart lowers the size by one. -/
theorem size_drop_one_add {p : Part} (h : p ≠ .nil) : (p.drop 1).size + 1 = p.size := by
  cases p with
  | nil => exact absurd rfl h
  | _ => simp [drop, size]

/-- The spoke of a shifted sector is that of the shifting sector. -/
theorem spoke_shift {p : Part} (h : p ≠ .nil) (q : Part) : (shift p q).spoke = p.spoke := by
  cases p with
  | nil => exact absurd rfl h
  | _ => rfl

/-- The hat of a shifted sector is that of the shifting sector. -/
theorem hat_shift {p : Part} (h : p ≠ .nil) (q : Part) : (shift p q).hat = p.hat := by
  cases p with
  | nil => exact absurd rfl h
  | _ => rfl

end Part

/-! ### Zipper validity -/

/-- The two sectors of a zipper concatenate to two copies of the part. -/
def Zvalid (p0r pl pr : Part) : Prop := pl.catrev pr = p0r.cat p0r

/-- The sectors of a zipper part are valid. -/
def Zpart.Valid (p0r : Part) (zp : Zpart) : Prop := Zvalid p0r zp.left zp.right

/-- Shifting a valid zipper to the right keeps it valid. -/
theorem Zvalid.shiftLeft {p0r pl pr : Part} (h : Zvalid p0r pl pr) :
    Zvalid p0r (pl.drop 1) (Part.shift pl pr) :=
  (Part.catrev_shift_left pl pr).symm.trans h

/-- Shifting a valid zipper to the left keeps it valid. -/
theorem Zvalid.shiftRight {p0r pl pr : Part} (h : Zvalid p0r pl pr) :
    Zvalid p0r (Part.shift pr pl) (pr.drop 1) :=
  (Part.catrev_shift_right pl pr).symm.trans h


/-! ### The dart a zipper names -/

namespace Hypermap

variable {D : Type*} [Finite D]

/-- The dart just before `y` on its face. -/
def facePred (G : Hypermap D) (y : D) : D := G.edge (G.node y)

omit [Finite D] in
/-- One face step undoes `facePred`. -/
@[simp] theorem face_facePred (G : Hypermap D) (y : D) : G.face (G.facePred y) = y := G.nodeK y

omit [Finite D] in
/-- `facePred` undoes one face step. -/
theorem facePred_face {G : Hypermap D} (hp : G.Plain) (y : D) : G.facePred (G.face y) = y := by
  change G.edge (G.node (G.face y)) = y
  rw [hp.node_face, hp.edge_edge]

/-- `facePred` stays on the same face. -/
@[simp] theorem arity_facePred (G : Hypermap D) (y : D) :
    G.arity (G.facePred y) = G.arity y := by
  conv_rhs => rw [← G.face_facePred y]
  rw [G.arity_face]

omit [Finite D] in
/-- Walking `m` steps backwards around a face of arity `k` is walking `k - m`
steps forwards. -/
theorem facePred_iterate {G : Hypermap D} {y : D} {k m : ℕ} (hk : G.arity y = k)
    (hm : m ≤ k) : G.facePred^[m] y = G.face^[k - m] y := by
  have h1 : ∀ (n : ℕ) (z : D), (G.face : D → D)^[n] (G.facePred^[n] z) = z := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply (G.facePred) n z,
        Function.iterate_succ_apply' (G.face : D → D) n _, ih, G.face_facePred]
  refine (Function.Injective.iterate G.face.injective m) ?_
  rw [h1 m y, ← Function.iterate_add_apply, Nat.add_sub_cancel' hm, ← hk,
    G.iterate_face_arity]

omit [Finite D] in
/-- Walking `m` steps backwards and `n` forwards around a face of arity `m + n`
returns to the start. -/
theorem facePred_iterate_add {G : Hypermap D} {y : D} {m n : ℕ} (hk : G.arity y = m + n) :
    G.facePred^[m] y = G.face^[n] y := by
  have h := facePred_iterate hk (Nat.le_add_right m n)
  rwa [Nat.add_sub_cancel_left] at h

/-- The dart named by the index `zi`, starting from the reference dart `x`. -/
def zmove (G : Hypermap D) : ZpartLoc → D → D
  | .nil, x => x
  | .hub, x => x
  | .hubl, x => G.node x
  | .hubr, x => G.node (G.node x)
  | .hat, x => G.node (G.edge (G.node (G.node x)))
  | .hatl, x => G.edge (G.node (G.node x))
  | .hatr, x => G.face (G.node (G.node x))
  | .fan0l, x => G.face (G.edge (G.facePred^[2] (G.node x)))
  | .fan1l, x => G.face (G.edge (G.facePred^[3] (G.node x)))
  | .fan2l, x => G.face (G.edge (G.facePred^[4] (G.node x)))
  | .fan3l, x => G.face (G.edge (G.facePred^[5] (G.node x)))
  | .fan0r, x => G.edge (G.face^[2] (G.node x))
  | .fan1r, x => G.edge (G.face^[3] (G.node x))
  | .fan2r, x => G.edge (G.face^[4] (G.node x))
  | .fan3r, x => G.edge (G.face^[5] (G.node x))

/-- The reference hub dart for a zipper with left sector `pl`. -/
def zorg (G : Hypermap D) (x0 : D) (pl : Part) : D := G.face^[pl.size] x0

/-- The dart a zipper part names. -/
def zdart (G : Hypermap D) (x0 : D) (zp : Zpart) : D := G.zmove zp.loc (G.zorg x0 zp.left)

/-- If the zipper is proper then it names the dart `x`. -/
def Zpfit (G : Hypermap D) (x0 x : D) (zp : Zpart) : Prop := zp.Proper → G.zdart x0 zp = x

/-! ### Arities of the zipper darts -/

variable {G : Hypermap D}

/-- The dart at `hubr` lies on the spoke face of the reference dart. -/
theorem arity_zmove_hubr (hc : G.Cubic) (x : D) :
    G.arity (G.zmove .hubr x) = G.arity (G.edge x) := by
  change G.arity (G.node (G.node x)) = _
  rw [hc.node_node, G.arity_face]

/-- The dart at `hatr` lies on the spoke face of the reference dart. -/
theorem arity_zmove_hatr (hc : G.Cubic) (x : D) :
    G.arity (G.zmove .hatr x) = G.arity (G.edge x) := by
  change G.arity (G.face (G.node (G.node x))) = _
  rw [G.arity_face, hc.node_node, G.arity_face]

/-- The dart at `hatl` lies on the spoke face of the previous reference dart. -/
theorem arity_zmove_hatl (G : Hypermap D) (x : D) :
    G.arity (G.zmove .hatl x) = G.arity (G.node x) :=
  G.arity_facePred (G.node x)

/-- The dart at `hat` lies on the hat face of the reference dart. -/
theorem arity_zmove_hat (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.arity (G.zmove .hat x) = G.ars 2 x := by
  have key : G.zmove .hat x = G.face (G.edge (G.face^[2] (G.edge x))) := by
    change G.node (G.edge (G.node (G.node x))) = _
    rw [hc.node_node, ← face_edge_face G hp hc (G.face (G.edge x))]
    rfl
  rw [key, G.arity_face]
  rfl

/-- The dart at `fan0l` lies on the hat face of the reference dart. -/
theorem arity_zmove_fan0l (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.arity (G.zmove .fan0l x) = G.ars 2 x := by
  have h1 : G.facePred (G.node x) = G.edge (G.face (G.edge x)) := by
    change G.edge (G.node (G.node x)) = _
    rw [hc.node_node]
  have h2 : G.facePred (G.edge (G.face (G.edge x)))
      = G.edge (G.face (G.edge (G.face^[2] (G.edge x)))) := by
    change G.edge (G.node (G.edge (G.face (G.edge x)))) = _
    rw [← face_edge_face G hp hc (G.face (G.edge x))]
    rfl
  have key : G.zmove .fan0l x = G.face (G.face (G.edge (G.face^[2] (G.edge x)))) := by
    change G.face (G.edge (G.facePred^[2] (G.node x))) = _
    rw [Function.iterate_succ_apply' G.facePred 1 (G.node x)]
    rw [Function.iterate_one, h1, h2, hp.edge_edge]
  rw [key, G.arity_face, G.arity_face]
  rfl

/-- A dart in the left fan chain lies on the face the part prescribes, once the
arity of the spoke face is known. -/
theorem arity_zmove_fanl {zi : ZpartLoc} (x : D) {m k : ℕ} (hk : G.arity (G.node x) = k)
    (hm : m ≤ k) (hz : G.zmove zi x = G.face (G.edge (G.facePred^[m] (G.node x)))) :
    G.arity (G.zmove zi x) = G.arity (G.edge (G.face^[k - m] (G.node x))) := by
  rw [hz, facePred_iterate hk hm, G.arity_face]

end Hypermap

/-! ### The range a part imposes at a zipper dart -/

/-- The range for the hub arity; a singleton unless the hub has more than
eight sides. -/
def hubRange : QArity → PRange
  | .qa5 => .pr55
  | .qa6 => .pr66
  | .qa7 => .pr77
  | .qa8 => .pr88
  | _ => .pr99

/-- The arity range the part imposes on the face of the zipper dart. -/
def zrange (ahub : QArity) : Zpart → PRange
  | ⟨.nil, _, _⟩ => .pr59
  | ⟨.hub, _, _⟩ => hubRange ahub
  | ⟨.hubl, pl, _⟩ => pl.spoke
  | ⟨.hubr, _, pr⟩ => pr.spoke
  | ⟨.hat, _, pr⟩ => pr.hat
  | ⟨.hatl, pl, _⟩ => pl.spoke
  | ⟨.hatr, _, pr⟩ => pr.spoke
  | ⟨.fan0l, _, pr⟩ => pr.hat
  | ⟨.fan1l, pl, _⟩ => pl.fan1L
  | ⟨.fan2l, pl, _⟩ => pl.fan2L
  | ⟨.fan3l, pl, _⟩ => pl.fan3L
  | ⟨.fan0r, pl, _⟩ => pl.hat
  | ⟨.fan1r, pl, _⟩ => pl.fan1R
  | ⟨.fan2r, pl, _⟩ => pl.fan2R
  | ⟨.fan3r, pl, _⟩ => pl.fan3R

namespace Hypermap

variable {D : Type*} [Finite D]

/-- The standing hypotheses of one step of the reducibility search: the map is
plain, cubic and pentagonal, `p0l` is the reversal of the part sector `p0r`,
and `x0` fits `p0r` exactly, with hub arity `ahub`. -/
structure Setup (G : Hypermap D) (ahub : QArity) (p0l p0r : Part) (x0 : D) : Prop where
  /-- The map is plain, cubic and pentagonal. -/
  geo : G.PlainCubicPentagonal
  /-- The left sector is the reversal of the right one. -/
  left_eq : p0l = p0r.rev
  /-- The reference dart fits the part exactly. -/
  fit : G.ExactFitp x0 p0r
  /-- The hub arity is the one the search is running for. -/
  arity_hub : G.arity x0 = ahub.toNat

omit [Finite D] in
/-- Turning the zipper origin one subpart back. -/
theorem zorg_drop {G : Hypermap D} (x0 : D) {pl : Part} (hpl : pl ≠ .nil) :
    G.zorg x0 pl = G.face (G.zorg x0 (pl.drop 1)) := by
  change G.face^[pl.size] x0 = G.face (G.face^[(pl.drop 1).size] x0)
  rw [← Part.size_drop_one_add hpl, Function.iterate_succ_apply']

omit [Finite D] in
/-- The spoke of the previous subpart, seen from the zipper origin. -/
theorem node_zorg {G : Hypermap D} (hp : G.Plain) (x0 : D) {pl : Part} (hpl : pl ≠ .nil) :
    G.node (G.zorg x0 pl) = G.edge (G.zorg x0 (pl.drop 1)) := by
  rw [zorg_drop x0 hpl, hp.node_face]

omit [Finite D] in
/-- The spoke range of a nonempty sector is met at its reference dart. -/
theorem mem_spoke_of_fitp {G : Hypermap D} {q : Part} {u : D} (hf : G.Fitp u q)
    (hq : q ≠ .nil) : q.spoke.Mem (G.arity (G.edge u)) := by
  cases q with
  | nil => exact absurd rfl hq
  | cons => exact hf.1
  | cons6 => exact hf.1
  | cons7 => exact hf.1
  | cons8 => exact hf.1

namespace Setup

variable {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}

omit [Finite D] in
/-- The map is plain. -/
theorem plain (hs : G.Setup ahub p0l p0r x0) : G.Plain := hs.geo.base.plain

omit [Finite D] in
/-- The map is cubic. -/
theorem cubic (hs : G.Setup ahub p0l p0r x0) : G.Cubic := hs.geo.base.cubic

omit [Finite D] in
/-- The map is pentagonal. -/
theorem pentagonal (hs : G.Setup ahub p0l p0r x0) : G.Pentagonal := hs.geo.pentagonal

omit [Finite D] in
/-- The free range holds at every dart of a pentagonal map. -/
theorem mem_pr59 (hs : G.Setup ahub p0l p0r x0) (y : D) : PRange.pr59.Mem (G.arity y) :=
  (PRange.mem_pr59 _).mpr (hs.pentagonal y)

omit [Finite D] in
/-- The right sector has the hub arity as its size. -/
theorem size_p0r (hs : G.Setup ahub p0l p0r x0) : p0r.size = ahub.toNat :=
  hs.fit.1.symm.trans hs.arity_hub

omit [Finite D] in
/-- The left sector has the hub arity as its size. -/
theorem size_p0l (hs : G.Setup ahub p0l p0r x0) : p0l.size = ahub.toNat := by
  rw [hs.left_eq, Part.size_rev]; exact hs.size_p0r

omit [Finite D] in
/-- The initial zipper is valid. -/
theorem zvalid_init (hs : G.Setup ahub p0l p0r x0) : Zvalid p0r p0l p0r := by
  change p0l.catrev p0r = p0r.cat p0r
  rw [hs.left_eq, Part.catrev_eq_cat, Part.rev_rev]

omit [Finite D] in
/-- A valid zipper describes the second neighbourhood of the reference dart. -/
theorem fitp_zvalid (hs : G.Setup ahub p0l p0r x0) {pl pr : Part} (h : Zvalid p0r pl pr) :
    G.Fitp x0 (pl.catrev pr) := by
  rw [show pl.catrev pr = p0r.cat p0r from h, G.fitp_cat]
  refine ⟨hs.fit.2, ?_⟩
  rw [hs.size_p0r, ← hs.arity_hub, G.iterate_face_arity]
  exact hs.fit.2

omit [Finite D] in
/-- The right sector of a valid zipper fits at the zipper origin. -/
theorem fitp_right (hs : G.Setup ahub p0l p0r x0) {pl pr : Part} (h : Zvalid p0r pl pr) :
    G.Fitp (G.zorg x0 pl) pr := by
  have := hs.fitp_zvalid h
  rw [G.fitp_catrev] at this
  exact this.2

omit [Finite D] in
/-- The first subpart of the left sector fits one subpart back. -/
theorem fitp_left (hs : G.Setup ahub p0l p0r x0) {pl pr : Part} (h : Zvalid p0r pl pr) :
    G.Fitp (G.zorg x0 (pl.drop 1)) (Part.shift pl pr) :=
  hs.fitp_right h.shiftLeft

end Setup

/-- The face of the zipper dart has the arity the part prescribes. -/
theorem zrange_dart {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}
    (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (h : zp.Valid p0r) :
    (zrange ahub zp).Mem (G.arity (G.zdart x0 zp)) := by
  obtain ⟨zi, pl, pr⟩ := zp
  have hp := hs.plain
  have hc := hs.cubic
  have hfree := hs.mem_pr59
  have hr : G.Fitp (G.zorg x0 pl) pr := hs.fitp_right h
  cases zi with
  | nil => exact hfree _
  | hub =>
    change (hubRange ahub).Mem (G.arity (G.zorg x0 pl))
    rw [show G.zorg x0 pl = G.face^[pl.size] x0 from rfl, G.arity_iterate_face, hs.arity_hub]
    cases ahub <;> decide
  | hubl =>
    change pl.spoke.Mem (G.arity (G.node (G.zorg x0 pl)))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    · rw [node_zorg hp x0 hpl, ← Part.spoke_shift hpl pr]
      exact mem_spoke_of_fitp (hs.fitp_left h) (Part.shift_ne_nil hpl pr)
  | hubr =>
    change pr.spoke.Mem (G.arity (G.zmove .hubr (G.zorg x0 pl)))
    by_cases hpr : pr = .nil
    · subst hpr; exact hfree _
    · rw [arity_zmove_hubr hc]
      exact mem_spoke_of_fitp hr hpr
  | hat =>
    change pr.hat.Mem (G.arity (G.zmove .hat (G.zorg x0 pl)))
    by_cases hpr : pr = .nil
    · subst hpr; exact hfree _
    · rw [arity_zmove_hat hp hc]
      exact G.fitp_hat .pr59 hr hpr
  | hatl =>
    change pl.spoke.Mem (G.arity (G.zmove .hatl (G.zorg x0 pl)))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    · rw [arity_zmove_hatl, node_zorg hp x0 hpl, ← Part.spoke_shift hpl pr]
      exact mem_spoke_of_fitp (hs.fitp_left h) (Part.shift_ne_nil hpl pr)
  | hatr =>
    change pr.spoke.Mem (G.arity (G.zmove .hatr (G.zorg x0 pl)))
    by_cases hpr : pr = .nil
    · subst hpr; exact hfree _
    · rw [arity_zmove_hatr hc]
      exact mem_spoke_of_fitp hr hpr
  | fan0l =>
    change pr.hat.Mem (G.arity (G.zmove .fan0l (G.zorg x0 pl)))
    by_cases hpr : pr = .nil
    · subst hpr; exact hfree _
    · rw [arity_zmove_fan0l hp hc]
      exact G.fitp_hat .pr59 hr hpr
  | fan0r =>
    change pl.hat.Mem (G.arity (G.edge (G.face^[2] (G.node (G.zorg x0 pl)))))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    · rw [node_zorg hp x0 hpl, ← Part.hat_shift hpl pr]
      exact G.fitp_hat .pr59 (hs.fitp_left h) (Part.shift_ne_nil hpl pr)
  | fan1r =>
    change pl.fan1R.Mem (G.arity (G.edge (G.face^[3] (G.node (G.zorg x0 pl)))))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    rw [node_zorg hp x0 hpl]
    have hl := hs.fitp_left h
    clear h hpl hr
    cases pl with
    | nil => exact hfree _
    | cons => exact hfree _
    | cons6 => exact hl.2.2.1
    | cons7 => exact hl.2.2.1
    | cons8 => exact hl.2.2.1
  | fan2r =>
    change pl.fan2R.Mem (G.arity (G.edge (G.face^[4] (G.node (G.zorg x0 pl)))))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    rw [node_zorg hp x0 hpl]
    have hl := hs.fitp_left h
    clear h hpl hr
    cases pl with
    | nil => exact hfree _
    | cons => exact hfree _
    | cons6 => exact hfree _
    | cons7 => exact hl.2.2.2.1
    | cons8 => exact hl.2.2.2.1
  | fan3r =>
    change pl.fan3R.Mem (G.arity (G.edge (G.face^[5] (G.node (G.zorg x0 pl)))))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    rw [node_zorg hp x0 hpl]
    have hl := hs.fitp_left h
    clear h hpl hr
    cases pl with
    | nil => exact hfree _
    | cons => exact hfree _
    | cons6 => exact hfree _
    | cons7 => exact hfree _
    | cons8 => exact hl.2.2.2.2.1
  | fan1l =>
    change pl.fan1L.Mem (G.arity (G.zmove .fan1l (G.zorg x0 pl)))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    have hn := node_zorg hp x0 hpl
    have hl := hs.fitp_left h
    clear h hpl hr
    cases pl with
    | nil => exact hfree _
    | cons => exact hfree _
    | cons6 hh f1 pl' =>
      have hk : G.arity (G.node (G.zorg x0 (Part.cons6 hh f1 pl'))) = 6 := by
        rw [hn]; exact (PRange.mem_pr66 _).mp hl.1
      rw [arity_zmove_fanl _ hk (by omega) rfl, hn]
      exact hl.2.2.1
    | cons7 hh f1 f2 pl' =>
      have hk : G.arity (G.node (G.zorg x0 (Part.cons7 hh f1 f2 pl'))) = 7 := by
        rw [hn]; exact (PRange.mem_pr77 _).mp hl.1
      rw [arity_zmove_fanl _ hk (by omega) rfl, hn]
      exact hl.2.2.2.1
    | cons8 hh f1 f2 f3 pl' =>
      have hk : G.arity (G.node (G.zorg x0 (Part.cons8 hh f1 f2 f3 pl'))) = 8 := by
        rw [hn]; exact (PRange.mem_pr88 _).mp hl.1
      rw [arity_zmove_fanl _ hk (by omega) rfl, hn]
      exact hl.2.2.2.2.1
  | fan2l =>
    change pl.fan2L.Mem (G.arity (G.zmove .fan2l (G.zorg x0 pl)))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    have hn := node_zorg hp x0 hpl
    have hl := hs.fitp_left h
    clear h hpl hr
    cases pl with
    | nil => exact hfree _
    | cons => exact hfree _
    | cons6 => exact hfree _
    | cons7 hh f1 f2 pl' =>
      have hk : G.arity (G.node (G.zorg x0 (Part.cons7 hh f1 f2 pl'))) = 7 := by
        rw [hn]; exact (PRange.mem_pr77 _).mp hl.1
      rw [arity_zmove_fanl _ hk (by omega) rfl, hn]
      exact hl.2.2.1
    | cons8 hh f1 f2 f3 pl' =>
      have hk : G.arity (G.node (G.zorg x0 (Part.cons8 hh f1 f2 f3 pl'))) = 8 := by
        rw [hn]; exact (PRange.mem_pr88 _).mp hl.1
      rw [arity_zmove_fanl _ hk (by omega) rfl, hn]
      exact hl.2.2.2.1
  | fan3l =>
    change pl.fan3L.Mem (G.arity (G.zmove .fan3l (G.zorg x0 pl)))
    by_cases hpl : pl = .nil
    · subst hpl; exact hfree _
    have hn := node_zorg hp x0 hpl
    have hl := hs.fitp_left h
    clear h hpl hr
    cases pl with
    | nil => exact hfree _
    | cons => exact hfree _
    | cons6 => exact hfree _
    | cons7 => exact hfree _
    | cons8 hh f1 f2 f3 pl' =>
      have hk : G.arity (G.node (G.zorg x0 (Part.cons8 hh f1 f2 f3 pl'))) = 8 := by
        rw [hn]; exact (PRange.mem_pr88 _).mp hl.1
      rw [arity_zmove_fanl _ hk (by omega) rfl, hn]
      exact hl.2.2.1

end Hypermap

/-! ### Shifting a zipper -/

/-- The zipper one subpart to the left, relocated at `zi`; it wraps around to
the initial zipper when the left sector runs out. -/
def zshiftl (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) : Zpart :=
  if zp.left = .nil then ⟨zi, p0l.drop 1, Part.shift p0l p0r⟩
  else if zp.left.size = 1 then ⟨zi, p0l, p0r⟩
  else ⟨zi, zp.left.drop 1, Part.shift zp.left zp.right⟩

/-- The zipper one subpart to the right, relocated at `zi`; it wraps around to
the initial zipper when the right sector runs out. -/
def zshiftr (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) : Zpart :=
  if zp.right = .nil then ⟨zi, Part.shift p0r p0l, p0r.drop 1⟩
  else if zp.right.size = 1 then ⟨zi, p0l, p0r⟩
  else ⟨zi, Part.shift zp.right zp.left, zp.right.drop 1⟩

@[simp] theorem loc_zshiftl (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) :
    (zshiftl p0l p0r zi zp).loc = zi := by
  unfold zshiftl; split_ifs <;> rfl

@[simp] theorem loc_zshiftr (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) :
    (zshiftr p0l p0r zi zp).loc = zi := by
  unfold zshiftr; split_ifs <;> rfl

/-! ### Zipper steps

`zstepL` and `zstepR` follow the left and right moves of a quiz around the
second neighbourhood of the hub. -/

/-- The left-most index in the left fan chain of the first subpart, or `nil`
when the spoke arity is not determined. -/
def zfanL : Part → ZpartLoc
  | .cons .pr55 _ _ => .fan0l
  | .cons6 _ _ _ => .fan1l
  | .cons7 _ _ _ _ => .fan2l
  | .cons8 _ _ _ _ _ => .fan3l
  | _ => .nil

/-- The right-most index in the right fan chain of the first subpart, or `nil`
when the spoke arity is not determined. -/
def zfanR : Part → ZpartLoc
  | .cons .pr55 _ _ => .fan0r
  | .cons6 _ _ _ => .fan1r
  | .cons7 _ _ _ _ => .fan2r
  | .cons8 _ _ _ _ _ => .fan3r
  | _ => .nil

/-- Shifting does not change the left fan index. -/
theorem zfanL_shift {p : Part} (h : p ≠ .nil) (q : Part) :
    zfanL (Part.shift p q) = zfanL p := by
  cases p with
  | nil => exact absurd rfl h
  | cons s hh p' => cases s <;> rfl
  | cons6 _ _ _ => rfl
  | cons7 _ _ _ _ => rfl
  | cons8 _ _ _ _ _ => rfl

/-- Shifting does not change the right fan index. -/
theorem zfanR_shift {p : Part} (h : p ≠ .nil) (q : Part) :
    zfanR (Part.shift p q) = zfanR p := by
  cases p with
  | nil => exact absurd rfl h
  | cons s hh p' => cases s <;> rfl
  | cons6 _ _ _ => rfl
  | cons7 _ _ _ _ => rfl
  | cons8 _ _ _ _ _ => rfl

/-- The zipper naming the dart reached by a left quiz step. -/
def zstepL (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨.hub, _, _⟩ => zshiftl p0l p0r .hubl zp
  | ⟨.hubl, pl, pr⟩ => ⟨.hat, pl, pr⟩
  | ⟨.hubr, _, _⟩ => zshiftr p0l p0r .hubr zp
  | ⟨.hat, _, pr⟩ => zshiftr p0l p0r (zfanL pr) zp
  | ⟨.hatl, pl, pr⟩ => ⟨zfanR pl, pl, pr⟩
  | ⟨.hatr, pl, pr⟩ => ⟨.hub, pl, pr⟩
  | ⟨.fan0l, pl, pr⟩ => ⟨.hatr, pl, pr⟩
  | ⟨.fan1l, pl, pr⟩ => ⟨.fan0l, pl, pr⟩
  | ⟨.fan2l, pl, pr⟩ => ⟨.fan1l, pl, pr⟩
  | ⟨.fan3l, pl, pr⟩ => ⟨.fan2l, pl, pr⟩
  | ⟨_, pl, pr⟩ => ⟨.nil, pl, pr⟩

/-- The zipper naming the dart reached by a right quiz step. -/
def zstepR (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨.hub, _, _⟩ => zshiftr p0l p0r .hubr zp
  | ⟨.hubl, _, _⟩ => zshiftl p0l p0r .hubl zp
  | ⟨.hubr, pl, pr⟩ => ⟨.hat, pl, pr⟩
  | ⟨.hat, pl, pr⟩ => ⟨zfanR pl, pl, pr⟩
  | ⟨.hatl, pl, pr⟩ => ⟨.hub, pl, pr⟩
  | ⟨.hatr, _, pr⟩ => zshiftr p0l p0r (zfanL pr) zp
  | ⟨.fan0r, _, _⟩ => zshiftl p0l p0r .hatl zp
  | ⟨.fan1r, pl, pr⟩ => ⟨.fan0r, pl, pr⟩
  | ⟨.fan2r, pl, pr⟩ => ⟨.fan1r, pl, pr⟩
  | ⟨.fan3r, pl, pr⟩ => ⟨.fan2r, pl, pr⟩
  | ⟨_, pl, pr⟩ => ⟨.nil, pl, pr⟩

/-- An improper zipper stays improper under a left step. -/
theorem proper_of_proper_stepL {p0l p0r : Part} {zp : Zpart}
    (h : (zstepL p0l p0r zp).Proper) : zp.Proper := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first | exact absurd rfl h | exact ZpartLoc.noConfusion

/-- An improper zipper stays improper under a right step. -/
theorem proper_of_proper_stepR {p0l p0r : Part} {zp : Zpart}
    (h : (zstepR p0l p0r zp).Proper) : zp.Proper := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first | exact absurd rfl h | exact ZpartLoc.noConfusion

/-- The hub arity is at least five. -/
theorem five_le_toNat (qa : QArity) : 5 ≤ qa.toNat := by
  cases qa <;> decide

/-- The range `pr55` pins the arity to five. -/
theorem mem_pr55_iff (n : ℕ) : PRange.pr55.Mem n ↔ n = 5 := by
  simp only [PRange.Mem, PRange.lo, PRange.hi]
  omega

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}

omit [Finite D] in
/-- In a plain cubic map, crossing an edge from a node. -/
theorem node_edge (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.node (G.edge y) = G.face (G.edge (G.face y)) := (face_edge_face G hp hc y).symm

omit [Finite D] in
/-- The node step, read as an edge step from the previous dart on the face. -/
theorem node_eq_edge_facePred (hp : G.Plain) (t : D) : G.node t = G.edge (G.facePred t) := by
  change _ = G.edge (G.edge (G.node t))
  rw [hp.edge_edge]

omit [Finite D] in
/-- A left quiz step is two backward face steps followed by an edge step. -/
theorem qstepL_eq (hp : G.Plain) (v : D) : G.qstepL v = G.edge (G.facePred^[2] v) := by
  change G.node (G.edge (G.node v)) = _
  rw [Function.iterate_succ_apply' G.facePred 1, Function.iterate_one,
    ← node_eq_edge_facePred hp]
  rfl

omit [Finite D] in
/-- The dart at `hat`, in closed form. -/
theorem zmove_hat_eq (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.zmove .hat x = G.face (G.edge (G.face^[2] (G.edge x))) := by
  change G.node (G.edge (G.node (G.node x))) = _
  rw [hc.node_node, ← face_edge_face G hp hc (G.face (G.edge x))]
  rfl

omit [Finite D] in
/-- A left step moves one position down the left fan chain. -/
theorem qstepL_face_edge_facePred (hp : G.Plain) (hc : G.Cubic) (t : D) :
    G.qstepL (G.face (G.edge (G.facePred t))) = G.face (G.edge t) := by
  change G.node (G.edge (G.node (G.face (G.edge (G.facePred t))))) = _
  rw [hp.node_face, hp.edge_edge]
  change G.node (G.edge (G.edge (G.node t))) = _
  rw [hp.edge_edge, hc.node_node]

omit [Finite D] in
/-- The left fan chain of a subpart reaches the third dart of its spoke face. -/
theorem zmove_zfanL {q : Part} {u : D} (hf : G.Fitp u q) (hne : zfanL q ≠ .nil) {y : D}
    (hy : G.node y = G.edge u) :
    G.zmove (zfanL q) y = G.face (G.edge (G.face^[3] (G.edge u))) := by
  cases q with
  | nil => exact absurd rfl hne
  | cons s hh q' =>
    revert hf hne
    cases s <;> intro hf hne <;> try exact absurd rfl hne
    have hk : G.arity (G.edge u) = 2 + 3 := (mem_pr55_iff _).mp hf.1
    change G.face (G.edge (G.facePred^[2] (G.node y))) = _
    rw [hy, facePred_iterate_add hk]
  | cons6 hh f1 q' =>
    have hk : G.arity (G.edge u) = 3 + 3 := (PRange.mem_pr66 _).mp hf.1
    change G.face (G.edge (G.facePred^[3] (G.node y))) = _
    rw [hy, facePred_iterate_add hk]
  | cons7 hh f1 f2 q' =>
    have hk : G.arity (G.edge u) = 4 + 3 := (PRange.mem_pr77 _).mp hf.1
    change G.face (G.edge (G.facePred^[4] (G.node y))) = _
    rw [hy, facePred_iterate_add hk]
  | cons8 hh f1 f2 f3 q' =>
    have hk : G.arity (G.edge u) = 5 + 3 := (PRange.mem_pr88 _).mp hf.1
    change G.face (G.edge (G.facePred^[5] (G.node y))) = _
    rw [hy, facePred_iterate_add hk]

omit [Finite D] in
/-- The right fan chain of a subpart reaches the third dart backwards along its
spoke face. -/
theorem zmove_zfanR {q : Part} {u : D} (hf : G.Fitp u q) (hne : zfanR q ≠ .nil) {y : D}
    (hy : G.node y = G.edge u) :
    G.zmove (zfanR q) y = G.edge (G.facePred^[3] (G.edge u)) := by
  cases q with
  | nil => exact absurd rfl hne
  | cons s hh q' =>
    revert hf hne
    cases s <;> intro hf hne <;> try exact absurd rfl hne
    have hk : G.arity (G.edge u) = 3 + 2 := (mem_pr55_iff _).mp hf.1
    change G.edge (G.face^[2] (G.node y)) = _
    rw [hy, facePred_iterate_add hk]
  | cons6 hh f1 q' =>
    have hk : G.arity (G.edge u) = 3 + 3 := (PRange.mem_pr66 _).mp hf.1
    change G.edge (G.face^[3] (G.node y)) = _
    rw [hy, facePred_iterate_add hk]
  | cons7 hh f1 f2 q' =>
    have hk : G.arity (G.edge u) = 3 + 4 := (PRange.mem_pr77 _).mp hf.1
    change G.edge (G.face^[4] (G.node y)) = _
    rw [hy, facePred_iterate_add hk]
  | cons8 hh f1 f2 f3 q' =>
    have hk : G.arity (G.edge u) = 3 + 5 := (PRange.mem_pr88 _).mp hf.1
    change G.edge (G.face^[5] (G.node y)) = _
    rw [hy, facePred_iterate_add hk]

/-! ### Validity and darts of the shifted zippers -/

omit [Finite D] in
/-- Shifting keeps a zipper valid. -/
theorem valid_zshiftl (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (zi : ZpartLoc)
    (h : zp.Valid p0r) : (zshiftl p0l p0r zi zp).Valid p0r := by
  unfold zshiftl
  split_ifs with h0 h1
  · exact hs.zvalid_init.shiftLeft
  · exact hs.zvalid_init
  · exact h.shiftLeft

omit [Finite D] in
/-- Shifting keeps a zipper valid. -/
theorem valid_zshiftr (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (zi : ZpartLoc)
    (h : zp.Valid p0r) : (zshiftr p0l p0r zi zp).Valid p0r := by
  unfold zshiftr
  split_ifs with h0 h1
  · exact hs.zvalid_init.shiftRight
  · exact hs.zvalid_init
  · exact h.shiftRight

/-- The dart of a left-shifted zipper. -/
theorem zdart_zshiftl (hs : G.Setup ahub p0l p0r x0) (zi : ZpartLoc) (zp : Zpart) :
    G.zdart x0 (zshiftl p0l p0r zi zp) = G.zmove zi (G.facePred (G.zorg x0 zp.left)) := by
  have hp := hs.plain
  unfold zshiftl Hypermap.zdart
  split_ifs with h0 h1
  · simp only [h0]
    congr 1
    change G.face^[(p0l.drop 1).size] x0 = G.facePred (G.face^[Part.nil.size] x0)
    rw [Part.size_drop, hs.size_p0l]
    change G.face^[ahub.toNat - 1] x0 = G.facePred x0
    exact G.iterate_face_pred x0 hs.arity_hub (by have := five_le_toNat ahub; omega)
  · congr 1
    change G.face^[p0l.size] x0 = G.facePred (G.face^[zp.left.size] x0)
    rw [hs.size_p0l, ← hs.arity_hub, G.iterate_face_arity, h1, Function.iterate_one,
      facePred_face hp]
  · congr 1
    change G.face^[(zp.left.drop 1).size] x0 = G.facePred (G.face^[zp.left.size] x0)
    rw [← Part.size_drop_one_add h0, Function.iterate_succ_apply', facePred_face hp]

omit [Finite D] in
/-- Sizes of the two sectors of a valid zipper. -/
theorem size_add_size_of_valid (hs : G.Setup ahub p0l p0r x0) {pl pr : Part}
    (h : Zvalid p0r pl pr) : pl.size + pr.size = ahub.toNat + ahub.toNat := by
  have := congrArg Part.size h
  rwa [Part.size_catrev, Part.size_cat, hs.size_p0r] at this

omit [Finite D] in
/-- The dart of a right-shifted zipper. -/
theorem zdart_zshiftr (hs : G.Setup ahub p0l p0r x0) (zi : ZpartLoc) {zp : Zpart}
    (h : zp.Valid p0r) :
    G.zdart x0 (zshiftr p0l p0r zi zp) = G.zmove zi (G.face (G.zorg x0 zp.left)) := by
  have hsz := size_add_size_of_valid hs h
  have hx0 : G.face^[ahub.toNat] x0 = x0 := by rw [← hs.arity_hub, G.iterate_face_arity]
  have hp0r : p0r ≠ .nil := by
    intro hcon
    have := hs.size_p0r
    rw [hcon] at this
    have := five_le_toNat ahub
    simp only [Part.size] at *
    omega
  unfold zshiftr Hypermap.zdart
  split_ifs with h0 h1
  · congr 1
    change G.face^[(Part.shift p0r p0l).size] x0 = G.face (G.face^[zp.left.size] x0)
    rw [Part.size_shift_of_ne_nil hp0r, hs.size_p0l]
    rw [h0] at hsz
    simp only [Part.size] at hsz
    have e1 : (G.face : D → D)^[ahub.toNat + ahub.toNat] x0 = x0 := by
      rw [Function.iterate_add_apply, hx0, hx0]
    have hl : zp.left.size = ahub.toNat + ahub.toNat := by omega
    rw [hl, e1, Function.iterate_succ_apply', hx0]
  · congr 1
    change G.face^[p0l.size] x0 = G.face (G.face^[zp.left.size] x0)
    rw [hs.size_p0l, hx0]
    have e1 : (G.face : D → D)^[ahub.toNat + ahub.toNat] x0 = x0 := by
      rw [Function.iterate_add_apply, hx0, hx0]
    have hl : zp.left.size.succ = ahub.toNat + ahub.toNat := by omega
    rw [← Function.iterate_succ_apply' (G.face : D → D), hl, e1]
  · congr 1
    change G.face^[(Part.shift zp.right zp.left).size] x0 = G.face (G.face^[zp.left.size] x0)
    rw [Part.size_shift_of_ne_nil h0, Function.iterate_succ_apply']

/-! ### Unfolding iterated face steps -/

omit [Finite D] in
/-- Two backward face steps. -/
theorem facePred_two (G : Hypermap D) (t : D) : G.facePred^[2] t = G.facePred (G.facePred t) :=
  Function.iterate_succ_apply' _ 1 t

omit [Finite D] in
/-- Three backward face steps. -/
theorem facePred_three (G : Hypermap D) (t : D) :
    G.facePred^[3] t = G.facePred (G.facePred^[2] t) := Function.iterate_succ_apply' _ 2 t

omit [Finite D] in
/-- Four backward face steps. -/
theorem facePred_four (G : Hypermap D) (t : D) :
    G.facePred^[4] t = G.facePred (G.facePred^[3] t) := Function.iterate_succ_apply' _ 3 t

omit [Finite D] in
/-- Five backward face steps. -/
theorem facePred_five (G : Hypermap D) (t : D) :
    G.facePred^[5] t = G.facePred (G.facePred^[4] t) := Function.iterate_succ_apply' _ 4 t

omit [Finite D] in
/-- Two face steps. -/
theorem face_two (G : Hypermap D) (t : D) : G.face^[2] t = G.face (G.face t) :=
  Function.iterate_succ_apply' _ 1 t

omit [Finite D] in
/-- Three face steps. -/
theorem face_three (G : Hypermap D) (t : D) : G.face^[3] t = G.face (G.face^[2] t) :=
  Function.iterate_succ_apply' _ 2 t

omit [Finite D] in
/-- Four face steps. -/
theorem face_four (G : Hypermap D) (t : D) : G.face^[4] t = G.face (G.face^[3] t) :=
  Function.iterate_succ_apply' _ 3 t

omit [Finite D] in
/-- Five face steps. -/
theorem face_five (G : Hypermap D) (t : D) : G.face^[5] t = G.face (G.face^[4] t) :=
  Function.iterate_succ_apply' _ 4 t

end Hypermap

/-- Normalise the permutation words occurring in zipper dart computations: all
iterated face steps are unfolded and every `node` is pushed onto an atom. -/
local macro "zsimp " h1:term ", " h2:term : tactic =>
  `(tactic| simp only [zstepL, zstepR, Hypermap.zdart, Hypermap.zmove, Hypermap.qstepL,
      Hypermap.qstepR, Hypermap.facePred, Hypermap.facePred_two, Hypermap.facePred_three,
      Hypermap.facePred_four, Hypermap.facePred_five, Hypermap.face_two, Hypermap.face_three,
      Hypermap.face_four, Hypermap.face_five, Hypermap.Plain.node_face $h1,
      Hypermap.Cubic.node_node $h2, Hypermap.node_edge $h1 $h2,
      Hypermap.Plain.edge_edge $h1, Hypermap.nodeK])

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}

omit [Finite D] in
/-- Validity is preserved by a left step. -/
theorem valid_stepL (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (h : zp.Valid p0r) :
    (zstepL p0l p0r zp).Valid p0r := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first
    | exact h
    | exact valid_zshiftl hs _ h
    | exact valid_zshiftr hs _ h

omit [Finite D] in
/-- Validity is preserved by a right step. -/
theorem valid_stepR (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (h : zp.Valid p0r) :
    (zstepR p0l p0r zp).Valid p0r := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first
    | exact h
    | exact valid_zshiftl hs _ h
    | exact valid_zshiftr hs _ h

/-- A left step of the zipper follows a left quiz step. -/
theorem zdart_stepL (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (h : zp.Valid p0r) :
    G.Zpfit x0 (G.qstepL (G.zdart x0 zp)) (zstepL p0l p0r zp) := by
  obtain ⟨zi, pl, pr⟩ := zp
  have hp := hs.plain
  have hc := hs.cubic
  have hv : Zvalid p0r pl pr := h
  intro hprop
  cases zi with
  | nil => exact absurd rfl hprop
  | hub =>
    rw [show zstepL p0l p0r ⟨.hub, pl, pr⟩ = zshiftl p0l p0r .hubl ⟨.hub, pl, pr⟩ from rfl,
      zdart_zshiftl hs]
    zsimp hp, hc
  | hubl => zsimp hp, hc
  | hubr =>
    rw [show zstepL p0l p0r ⟨.hubr, pl, pr⟩ = zshiftr p0l p0r .hubr ⟨.hubr, pl, pr⟩ from rfl,
      zdart_zshiftr hs _ h]
    zsimp hp, hc
  | hat =>
    simp only [Zpart.Proper, zstepL, loc_zshiftr, ne_eq] at hprop
    rw [show zstepL p0l p0r ⟨.hat, pl, pr⟩ = zshiftr p0l p0r (zfanL pr) ⟨.hat, pl, pr⟩ from rfl,
      zdart_zshiftr hs _ h,
      zmove_zfanL (hs.fitp_right hv) hprop (hp.node_face (G.zorg x0 pl))]
    zsimp hp, hc
  | hatl =>
    have hne : zfanR pl ≠ .nil := hprop
    have hpl : pl ≠ .nil := by rintro rfl; exact hne rfl
    rw [show zstepL p0l p0r ⟨.hatl, pl, pr⟩ = ⟨zfanR pl, pl, pr⟩ from rfl]
    change G.zmove (zfanR pl) (G.zorg x0 pl) = _
    rw [← zfanR_shift hpl pr,
      zmove_zfanR (hs.fitp_left hv) (by rwa [zfanR_shift hpl]) (node_zorg hp x0 hpl),
      ← node_zorg hp x0 hpl]
    zsimp hp, hc
  | hatr => zsimp hp, hc
  | fan0l => zsimp hp, hc
  | fan1l => zsimp hp, hc
  | fan2l => zsimp hp, hc
  | fan3l => zsimp hp, hc
  | fan0r => exact absurd rfl hprop
  | fan1r => exact absurd rfl hprop
  | fan2r => exact absurd rfl hprop
  | fan3r => exact absurd rfl hprop

/-- A right step of the zipper follows a right quiz step. -/
theorem zdart_stepR (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (h : zp.Valid p0r) :
    G.Zpfit x0 (G.qstepR (G.zdart x0 zp)) (zstepR p0l p0r zp) := by
  obtain ⟨zi, pl, pr⟩ := zp
  have hp := hs.plain
  have hc := hs.cubic
  have hv : Zvalid p0r pl pr := h
  intro hprop
  cases zi with
  | nil => exact absurd rfl hprop
  | hub =>
    rw [show zstepR p0l p0r ⟨.hub, pl, pr⟩ = zshiftr p0l p0r .hubr ⟨.hub, pl, pr⟩ from rfl,
      zdart_zshiftr hs _ h]
    zsimp hp, hc
  | hubl =>
    rw [show zstepR p0l p0r ⟨.hubl, pl, pr⟩ = zshiftl p0l p0r .hubl ⟨.hubl, pl, pr⟩ from rfl,
      zdart_zshiftl hs]
    zsimp hp, hc
  | hubr => zsimp hp, hc
  | hat =>
    have hne : zfanR pl ≠ .nil := hprop
    have hpl : pl ≠ .nil := by rintro rfl; exact hne rfl
    rw [show zstepR p0l p0r ⟨.hat, pl, pr⟩ = ⟨zfanR pl, pl, pr⟩ from rfl]
    change G.zmove (zfanR pl) (G.zorg x0 pl) = _
    rw [← zfanR_shift hpl pr,
      zmove_zfanR (hs.fitp_left hv) (by rwa [zfanR_shift hpl]) (node_zorg hp x0 hpl),
      ← node_zorg hp x0 hpl]
    zsimp hp, hc
  | hatl => zsimp hp, hc
  | hatr =>
    simp only [Zpart.Proper, zstepR, loc_zshiftr, ne_eq] at hprop
    rw [show zstepR p0l p0r ⟨.hatr, pl, pr⟩ = zshiftr p0l p0r (zfanL pr) ⟨.hatr, pl, pr⟩ from rfl,
      zdart_zshiftr hs _ h,
      zmove_zfanL (hs.fitp_right hv) hprop (hp.node_face (G.zorg x0 pl))]
    zsimp hp, hc
  | fan0l => exact absurd rfl hprop
  | fan1l => exact absurd rfl hprop
  | fan2l => exact absurd rfl hprop
  | fan3l => exact absurd rfl hprop
  | fan0r =>
    rw [show zstepR p0l p0r ⟨.fan0r, pl, pr⟩ = zshiftl p0l p0r .hatl ⟨.fan0r, pl, pr⟩ from rfl,
      zdart_zshiftl hs]
    zsimp hp, hc
  | fan1r => zsimp hp, hc
  | fan2r => zsimp hp, hc
  | fan3r => zsimp hp, hc

end Hypermap

/-! ### Top arities of a range -/

/-- The top qarity of a range; `qa9` when the range is unbounded. -/
def topqa : PRange → QArity
  | .pr55 => .qa5
  | .pr56 | .pr66 => .qa6
  | .pr57 | .pr67 | .pr77 => .qa7
  | .pr58 | .pr68 | .pr78 | .pr88 => .qa8
  | _ => .qa9

/-- The top qarity of the range `r` is `qa`, and it is at most eight. -/
def Fitqa (r : PRange) (qa : QArity) : Prop := qa.toNat ≤ 8 ∧ qa.toNat = (topqa r).toNat

instance (r : PRange) (qa : QArity) : Decidable (Fitqa r qa) := by unfold Fitqa; infer_instance

/-- The range `r` with its top value removed; `pr99` when `r` is unbounded or a
singleton. -/
def popqa : PRange → PRange
  | .pr56 => .pr55
  | .pr57 => .pr56
  | .pr58 => .pr57
  | .pr67 => .pr66
  | .pr68 => .pr67
  | .pr78 => .pr77
  | _ => .pr99

/-- An arity in `r` that is not in `popqa r` is the top of `r`. -/
theorem eq_of_fitqa {r : PRange} {qa : QArity} (h : Fitqa r qa) {n : ℕ} (hn : r.Mem n)
    (hpop : (popqa r).Mem 9 ∨ ¬ (popqa r).Mem n) : n = qa.toNat := by
  obtain ⟨h8, htop⟩ := h
  revert h8 htop hn hpop
  cases r <;> cases qa <;>
    simp only [topqa, popqa, QArity.toNat, PRange.Mem, PRange.lo, PRange.hi] <;> omega

/-- An improper zipper has an unbounded range, so it never matches a qarity. -/
theorem proper_of_fitqa {ahub : QArity} {zp : Zpart} {qa : QArity}
    (h : Fitqa (zrange ahub zp) qa) : zp.Proper := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi with
  | nil =>
    obtain ⟨h8, htop⟩ := h
    revert h8 htop
    cases qa <;> simp only [zrange, topqa, QArity.toNat] <;> omega
  | _ => exact ZpartLoc.noConfusion

/-! ### Zipper steps at the top of a range -/

/-- The left-most index in the left fan chain, assuming the spoke arity is the
top of its range. -/
def zfanLt : Part → ZpartLoc
  | .cons .pr55 _ _ => .fan0l
  | .cons .pr56 _ _ => .fan1l
  | .cons .pr66 _ _ => .fan1l
  | .cons6 _ _ _ => .fan1l
  | .cons7 _ _ _ _ => .fan2l
  | .cons8 _ _ _ _ _ => .fan3l
  | _ => .nil

/-- The right-most index in the right fan chain, assuming the spoke arity is
the top of its range. -/
def zfanRt : Part → ZpartLoc
  | .cons .pr55 _ _ => .fan0r
  | .cons .pr56 _ _ => .fan1r
  | .cons .pr66 _ _ => .fan1r
  | .cons6 _ _ _ => .fan1r
  | .cons7 _ _ _ _ => .fan2r
  | .cons8 _ _ _ _ _ => .fan3r
  | _ => .nil

/-- The zipper naming the dart reached by a left quiz step, when the arity at
the zipper dart is the top of its range. -/
def zstepLt (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨.hatl, pl, pr⟩ => ⟨zfanRt pl, pl, pr⟩
  | zp => zstepL p0l p0r zp

/-- The zipper naming the dart reached by a right quiz step, when the arity at
the zipper dart is the top of its range. -/
def zstepRt (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨.hatr, _, pr⟩ => zshiftr p0l p0r (zfanLt pr) zp
  | zp => zstepR p0l p0r zp

/-- An improper zipper stays improper under a left step. -/
theorem proper_of_proper_stepLt {p0l p0r : Part} {zp : Zpart}
    (h : (zstepLt p0l p0r zp).Proper) : zp.Proper := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first | exact absurd rfl h | exact ZpartLoc.noConfusion

/-- An improper zipper stays improper under a right step. -/
theorem proper_of_proper_stepRt {p0l p0r : Part} {zp : Zpart}
    (h : (zstepRt p0l p0r zp).Proper) : zp.Proper := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first | exact absurd rfl h | exact ZpartLoc.noConfusion

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}

/-- The arity at the zipper dart is the top of the range the part prescribes;
this is the precondition of the `t` variants of the zipper steps. -/
def ZpfitTop (G : Hypermap D) (ahub : QArity) (x0 : D) (zp : Zpart) : Prop :=
  G.arity (G.zdart x0 zp) = (topqa (zrange ahub zp)).toNat

omit [Finite D] in
/-- The left fan chain reaches the third dart of the spoke face, given the
spoke arity. -/
theorem zmove_zfanLt {q : Part} {u : D} (hk : G.arity (G.edge u) = (topqa q.spoke).toNat)
    (hne : zfanLt q ≠ .nil) {y : D} (hy : G.node y = G.edge u) :
    G.zmove (zfanLt q) y = G.face (G.edge (G.face^[3] (G.edge u))) := by
  cases q with
  | nil => exact absurd rfl hne
  | cons s hh q' =>
    revert hk hne
    cases s <;> intro hk hne <;> try exact absurd rfl hne
    case pr55 =>
      change G.face (G.edge (G.facePred^[2] (G.node y))) = _
      rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 2 + 3 from hk)]
    case pr66 =>
      change G.face (G.edge (G.facePred^[3] (G.node y))) = _
      rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 3 from hk)]
    case pr56 =>
      change G.face (G.edge (G.facePred^[3] (G.node y))) = _
      rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 3 from hk)]
  | cons6 hh f1 q' =>
    change G.face (G.edge (G.facePred^[3] (G.node y))) = _
    rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 3 from hk)]
  | cons7 hh f1 f2 q' =>
    change G.face (G.edge (G.facePred^[4] (G.node y))) = _
    rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 4 + 3 from hk)]
  | cons8 hh f1 f2 f3 q' =>
    change G.face (G.edge (G.facePred^[5] (G.node y))) = _
    rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 5 + 3 from hk)]

omit [Finite D] in
/-- The right fan chain reaches the third dart backwards along the spoke face,
given the spoke arity. -/
theorem zmove_zfanRt {q : Part} {u : D} (hk : G.arity (G.edge u) = (topqa q.spoke).toNat)
    (hne : zfanRt q ≠ .nil) {y : D} (hy : G.node y = G.edge u) :
    G.zmove (zfanRt q) y = G.edge (G.facePred^[3] (G.edge u)) := by
  cases q with
  | nil => exact absurd rfl hne
  | cons s hh q' =>
    revert hk hne
    cases s <;> intro hk hne <;> try exact absurd rfl hne
    case pr55 =>
      change G.edge (G.face^[2] (G.node y)) = _
      rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 2 from hk)]
    case pr66 =>
      change G.edge (G.face^[3] (G.node y)) = _
      rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 3 from hk)]
    case pr56 =>
      change G.edge (G.face^[3] (G.node y)) = _
      rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 3 from hk)]
  | cons6 hh f1 q' =>
    change G.edge (G.face^[3] (G.node y)) = _
    rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 3 from hk)]
  | cons7 hh f1 f2 q' =>
    change G.edge (G.face^[4] (G.node y)) = _
    rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 4 from hk)]
  | cons8 hh f1 f2 f3 q' =>
    change G.edge (G.face^[5] (G.node y)) = _
    rw [hy, facePred_iterate_add (show G.arity (G.edge u) = 3 + 5 from hk)]

omit [Finite D] in
/-- Validity is preserved by a left step at the top of a range. -/
theorem valid_stepLt (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (h : zp.Valid p0r) :
    (zstepLt p0l p0r zp).Valid p0r := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first
    | exact h
    | exact valid_zshiftl hs _ h
    | exact valid_zshiftr hs _ h

omit [Finite D] in
/-- Validity is preserved by a right step at the top of a range. -/
theorem valid_stepRt (hs : G.Setup ahub p0l p0r x0) {zp : Zpart} (h : zp.Valid p0r) :
    (zstepRt p0l p0r zp).Valid p0r := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> first
    | exact h
    | exact valid_zshiftl hs _ h
    | exact valid_zshiftr hs _ h

/-- A left step at the top of a range follows a left quiz step. -/
theorem zdart_stepLt (hs : G.Setup ahub p0l p0r x0) {zp : Zpart}
    (htop : G.ZpfitTop ahub x0 zp) (h : zp.Valid p0r) :
    G.Zpfit x0 (G.qstepL (G.zdart x0 zp)) (zstepLt p0l p0r zp) := by
  obtain ⟨zi, pl, pr⟩ := zp
  have hp := hs.plain
  have hv : Zvalid p0r pl pr := h
  intro hprop
  cases zi with
  | hatl =>
    have hne : zfanRt pl ≠ .nil := hprop
    have hpl : pl ≠ .nil := by rintro rfl; exact hne rfl
    have hk : G.arity (G.edge (G.zorg x0 (pl.drop 1))) = (topqa pl.spoke).toNat := by
      rw [← node_zorg hp x0 hpl, ← arity_zmove_hatl G (G.zorg x0 pl)]
      exact htop
    rw [show zstepLt p0l p0r ⟨.hatl, pl, pr⟩ = ⟨zfanRt pl, pl, pr⟩ from rfl]
    change G.zmove (zfanRt pl) (G.zorg x0 pl) = _
    rw [zmove_zfanRt hk hne (node_zorg hp x0 hpl), ← node_zorg hp x0 hpl]
    zsimp hp, hs.cubic
  | _ => exact zdart_stepL hs h hprop

/-- A right step at the top of a range follows a right quiz step. -/
theorem zdart_stepRt (hs : G.Setup ahub p0l p0r x0) {zp : Zpart}
    (htop : G.ZpfitTop ahub x0 zp) (h : zp.Valid p0r) :
    G.Zpfit x0 (G.qstepR (G.zdart x0 zp)) (zstepRt p0l p0r zp) := by
  obtain ⟨zi, pl, pr⟩ := zp
  have hp := hs.plain
  have hc := hs.cubic
  have hv : Zvalid p0r pl pr := h
  intro hprop
  cases zi with
  | hatr =>
    simp only [Zpart.Proper, zstepRt, loc_zshiftr, ne_eq] at hprop
    have hk : G.arity (G.edge (G.zorg x0 pl)) = (topqa pr.spoke).toNat := by
      rw [← arity_zmove_hatr hc (G.zorg x0 pl)]
      exact htop
    rw [show zstepRt p0l p0r ⟨.hatr, pl, pr⟩ = zshiftr p0l p0r (zfanLt pr) ⟨.hatr, pl, pr⟩ from rfl,
      zdart_zshiftr hs _ h, zmove_zfanLt hk hprop (hp.node_face (G.zorg x0 pl))]
    zsimp hp, hc
  | _ => exact zdart_stepR hs h hprop

end Hypermap

/-! ### Popping a range

When a quiz matches the top of an arity range, the check recurses on the part
in which that range has been replaced by its lower part. -/

section RedPop

variable (redRec : Part → Bool) (ahub : QArity) (p0r : Part)

/-- The recursive check on the part obtained by popping the range `r` of the
subpart built by `pc`; vacuously true when `r` is unbounded or a singleton. -/
def redPcons (pc : PRange → Part → Part) (r : PRange) (pr : Part) : Bool :=
  match r with
  | .pr56 => redRec (Part.take ahub.toNat ((pc .pr55 pr).cat p0r))
  | .pr57 => redRec (Part.take ahub.toNat ((pc .pr56 pr).cat p0r))
  | .pr58 => redRec (Part.take ahub.toNat ((pc .pr57 pr).cat p0r))
  | .pr67 => redRec (Part.take ahub.toNat ((pc .pr66 pr).cat p0r))
  | .pr68 => redRec (Part.take ahub.toNat ((pc .pr67 pr).cat p0r))
  | .pr78 => redRec (Part.take ahub.toNat ((pc .pr77 pr).cat p0r))
  | _ => true

/-- Pop the spoke range of the right sector. -/
def redPoprSpoke : Part → Bool
  | .cons s h p => redPcons redRec ahub p0r (fun r => .cons r h) s p
  | _ => true

/-- Pop the hat range of the right sector. -/
def redPoprHat : Part → Bool
  | .cons s h p => redPcons redRec ahub p0r (fun r => .cons s r) h p
  | .cons6 h f1 p => redPcons redRec ahub p0r (fun r => .cons6 r f1) h p
  | .cons7 h f1 f2 p => redPcons redRec ahub p0r (fun r => .cons7 r f1 f2) h p
  | .cons8 h f1 f2 f3 p => redPcons redRec ahub p0r (fun r => .cons8 r f1 f2 f3) h p
  | .nil => true

/-- Pop the spoke range of the left sector. -/
def redPoplSpoke : Part → Part → Bool
  | .cons s h _, pr => redPcons redRec ahub p0r (fun r => .cons r h) s pr
  | _, _ => true

/-- Pop the hat range of the left sector. -/
def redPoplHat : Part → Part → Bool
  | .cons s h _, pr => redPcons redRec ahub p0r (fun r => .cons s r) h pr
  | .cons6 h f1 _, pr => redPcons redRec ahub p0r (fun r => .cons6 r f1) h pr
  | .cons7 h f1 f2 _, pr => redPcons redRec ahub p0r (fun r => .cons7 r f1 f2) h pr
  | .cons8 h f1 f2 f3 _, pr => redPcons redRec ahub p0r (fun r => .cons8 r f1 f2 f3) h pr
  | .nil, _ => true

/-- Pop the range of the first clockwise fan of the left sector. -/
def redPoplFan1L : Part → Part → Bool
  | .cons6 h f1 _, pr => redPcons redRec ahub p0r (fun r => .cons6 h r) f1 pr
  | .cons7 h f1 f2 _, pr => redPcons redRec ahub p0r (fun r => .cons7 h f1 r) f2 pr
  | .cons8 h f1 f2 f3 _, pr => redPcons redRec ahub p0r (fun r => .cons8 h f1 f2 r) f3 pr
  | _, _ => true

/-- Pop the range of the second clockwise fan of the left sector. -/
def redPoplFan2L : Part → Part → Bool
  | .cons7 h f1 f2 _, pr => redPcons redRec ahub p0r (fun r => .cons7 h r f2) f1 pr
  | .cons8 h f1 f2 f3 _, pr => redPcons redRec ahub p0r (fun r => .cons8 h f1 r f3) f2 pr
  | _, _ => true

/-- Pop the range of the third clockwise fan of the left sector. -/
def redPoplFan3L : Part → Part → Bool
  | .cons8 h f1 f2 f3 _, pr => redPcons redRec ahub p0r (fun r => .cons8 h r f2 f3) f1 pr
  | _, _ => true

/-- Pop the range of the first counterclockwise fan of the left sector. -/
def redPoplFan1R : Part → Part → Bool
  | .cons6 h f1 _, pr => redPcons redRec ahub p0r (fun r => .cons6 h r) f1 pr
  | .cons7 h f1 f2 _, pr => redPcons redRec ahub p0r (fun r => .cons7 h r f2) f1 pr
  | .cons8 h f1 f2 f3 _, pr => redPcons redRec ahub p0r (fun r => .cons8 h r f2 f3) f1 pr
  | _, _ => true

/-- Pop the range of the second counterclockwise fan of the left sector. -/
def redPoplFan2R : Part → Part → Bool
  | .cons7 h f1 f2 _, pr => redPcons redRec ahub p0r (fun r => .cons7 h f1 r) f2 pr
  | .cons8 h f1 f2 f3 _, pr => redPcons redRec ahub p0r (fun r => .cons8 h f1 r f3) f2 pr
  | _, _ => true

/-- Pop the range of the third counterclockwise fan of the left sector. -/
def redPoplFan3R : Part → Part → Bool
  | .cons8 h f1 f2 f3 _, pr => redPcons redRec ahub p0r (fun r => .cons8 h f1 f2 r) f3 pr
  | _, _ => true

/-- Pop the range the part imposes at the zipper dart. -/
def redPop : Zpart → Bool
  | ⟨.hubl, pl, pr⟩ => redPoplSpoke redRec ahub p0r pl pr
  | ⟨.hubr, _, pr⟩ => redPoprSpoke redRec ahub p0r pr
  | ⟨.hatl, pl, pr⟩ => redPoplSpoke redRec ahub p0r pl pr
  | ⟨.hat, _, pr⟩ => redPoprHat redRec ahub p0r pr
  | ⟨.hatr, _, pr⟩ => redPoprSpoke redRec ahub p0r pr
  | ⟨.fan0l, _, pr⟩ => redPoprHat redRec ahub p0r pr
  | ⟨.fan1l, pl, pr⟩ => redPoplFan1L redRec ahub p0r pl pr
  | ⟨.fan2l, pl, pr⟩ => redPoplFan2L redRec ahub p0r pl pr
  | ⟨.fan3l, pl, pr⟩ => redPoplFan3L redRec ahub p0r pl pr
  | ⟨.fan0r, pl, pr⟩ => redPoplHat redRec ahub p0r pl pr
  | ⟨.fan1r, pl, pr⟩ => redPoplFan1R redRec ahub p0r pl pr
  | ⟨.fan2r, pl, pr⟩ => redPoplFan2R redRec ahub p0r pl pr
  | ⟨.fan3r, pl, pr⟩ => redPoplFan3R redRec ahub p0r pl pr
  | _ => true

end RedPop

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}
variable {redRec : Part → Bool}

/-- The hypothesis on the recursive check: it fails on every part that some
dart of the right hub arity fits exactly. -/
def NotRedRec (G : Hypermap D) (redRec : Part → Bool) (ahub : QArity) : Prop :=
  ∀ (y : D) (p : Part), G.arity y = ahub.toNat → G.ExactFitp y p → redRec p = false

/-- The arity of the zipper origin is the hub arity. -/
theorem arity_zorg (hs : G.Setup ahub p0l p0r x0) (pl : Part) :
    G.arity (G.zorg x0 pl) = ahub.toNat := by
  change G.arity (G.face^[pl.size] x0) = _
  rw [G.arity_iterate_face, hs.arity_hub]

/-- If a range matched the top of a subpart and the popped part is rejected by
the recursive check, then the arity at that location is that top value. -/
theorem redPcons_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {fc : PRange → Part → Part} {i : SubpartLoc} (hu : G.PartUpdate fc i)
    {r : PRange} {pl pr : Part} (hval : Zvalid p0r pl (fc r pr))
    {qa : QArity} (hqa : Fitqa r qa)
    (hred : redPcons redRec ahub p0r fc r pr = true) :
    G.arity (i.dart G (G.zorg x0 pl)) = qa.toNat := by
  have hy : G.arity (G.zorg x0 pl) = ahub.toNat := arity_zorg hs pl
  have hfit : G.Fitp (G.zorg x0 pl) (fc r pr) := hs.fitp_right hval
  have hsz : pl.size + (fc r pr).size = ahub.toNat + ahub.toNat :=
    size_add_size_of_valid hs hval
  have hmem : r.Mem (G.arity (i.dart G (G.zorg x0 pl))) := hu.mem_of_fitp r pr _ hfit
  have key : ∀ r' : PRange, redRec (Part.take ahub.toNat ((fc r' pr).cat p0r)) = true →
      ¬ r'.Mem (G.arity (i.dart G (G.zorg x0 pl))) := by
    intro r' hred' hmem'
    have hfit' : G.Fitp (G.zorg x0 pl) (fc r' pr) := hu.fitp_of_mem r r' pr _ hfit hmem'
    have hszr : (fc r' pr).size = (fc r pr).size := by rw [hu.size_eq, hu.size_eq]
    have hcat : G.Fitp (G.zorg x0 pl) ((fc r' pr).cat p0r) := by
      rw [G.fitp_cat]
      refine ⟨hfit', ?_⟩
      change G.Fitp (G.face^[(fc r' pr).size] (G.face^[pl.size] x0)) p0r
      rw [← Function.iterate_add_apply, hszr]
      have hadd : (fc r pr).size + pl.size = ahub.toNat + ahub.toNat := by omega
      rw [hadd, Function.iterate_add_apply, ← hs.arity_hub, G.iterate_face_arity,
        G.iterate_face_arity]
      exact hs.fit.2
    have hsize : (Part.take ahub.toNat ((fc r' pr).cat p0r)).size = ahub.toNat := by
      rw [Part.size_take, Part.size_cat, hs.size_p0r]
      omega
    have hexact : G.ExactFitp (G.zorg x0 pl) (Part.take ahub.toNat ((fc r' pr).cat p0r)) := by
      refine ⟨by rw [hy, hsize], ?_⟩
      have hc := hcat
      rw [← Part.cat_take_drop ahub.toNat ((fc r' pr).cat p0r), G.fitp_cat] at hc
      exact hc.1
    have hfalse := hrec _ _ hy hexact
    rw [hred'] at hfalse
    exact Bool.noConfusion hfalse
  refine eq_of_fitqa hqa hmem ?_
  cases r <;> first | exact Or.inl (by decide) | exact Or.inr (key _ hred)

/-- The arity of a dart in the left fan chain, given the arity of the spoke it
runs around. -/
theorem arity_zmove_fanl_zorg (hp : G.Plain) {zi : ZpartLoc} {pl : Part} {x0 : D}
    (hpl : pl ≠ .nil) {m n : ℕ}
    (hk : G.arity (G.edge (G.zorg x0 (pl.drop 1))) = m + n)
    (hz : G.zmove zi (G.zorg x0 pl)
      = G.face (G.edge (G.facePred^[m] (G.node (G.zorg x0 pl))))) :
    G.arity (G.zmove zi (G.zorg x0 pl))
      = G.arity (G.edge (G.face^[n] (G.edge (G.zorg x0 (pl.drop 1))))) := by
  rw [hz, node_zorg hp x0 hpl, facePred_iterate_add hk, G.arity_face]

/-- Popping the spoke of the right sector. -/
theorem redPoprSpoke_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pr.spoke qa)
    (hred : redPoprSpoke redRec ahub p0r pr = true) :
    G.arity (G.edge (G.zorg x0 pl)) = qa.toNat := by
  cases pr with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h p => exact redPcons_fit hs hrec (G.updateSpoke h) hval hqa hred
  | cons6 h f1 p =>
    obtain ⟨h8, htop⟩ := hqa
    have hq : qa.toNat = 6 := htop
    have hk : G.arity (G.edge (G.zorg x0 pl)) = 6 :=
      (PRange.mem_pr66 _).mp (hs.fitp_right hval).1
    omega
  | cons7 h f1 f2 p =>
    obtain ⟨h8, htop⟩ := hqa
    have hq : qa.toNat = 7 := htop
    have hk : G.arity (G.edge (G.zorg x0 pl)) = 7 :=
      (PRange.mem_pr77 _).mp (hs.fitp_right hval).1
    omega
  | cons8 h f1 f2 f3 p =>
    obtain ⟨h8, htop⟩ := hqa
    have hq : qa.toNat = 8 := htop
    have hk : G.arity (G.edge (G.zorg x0 pl)) = 8 :=
      (PRange.mem_pr88 _).mp (hs.fitp_right hval).1
    omega

/-- Popping the hat of the right sector. -/
theorem redPoprHat_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pr.hat qa)
    (hred : redPoprHat redRec ahub p0r pr = true) :
    G.arity (G.edge (G.face^[2] (G.edge (G.zorg x0 pl)))) = qa.toNat := by
  cases pr with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h p => exact redPcons_fit hs hrec (G.updateHat s) hval hqa hred
  | cons6 h f1 p => exact redPcons_fit hs hrec (G.update6Hat f1) hval hqa hred
  | cons7 h f1 f2 p => exact redPcons_fit hs hrec (G.update7Hat f1 f2) hval hqa hred
  | cons8 h f1 f2 f3 p => exact redPcons_fit hs hrec (G.update8Hat f1 f2 f3) hval hqa hred

/-- Popping the spoke of the left sector. -/
theorem redPoplSpoke_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.spoke qa)
    (hred : redPoplSpoke redRec ahub p0r pl pr = true) :
    G.arity (G.node (G.zorg x0 pl)) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' =>
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.updateSpoke h) hval.shiftLeft hqa hred
  | cons6 h f1 pl' =>
    obtain ⟨h8, htop⟩ := hqa
    have hq : qa.toNat = 6 := htop
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons6 h f1 pl').drop 1))) = 6 :=
      (PRange.mem_pr66 _).mp (hs.fitp_left hval).1
    rw [node_zorg hp x0 (by simp)]
    omega
  | cons7 h f1 f2 pl' =>
    obtain ⟨h8, htop⟩ := hqa
    have hq : qa.toNat = 7 := htop
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons7 h f1 f2 pl').drop 1))) = 7 :=
      (PRange.mem_pr77 _).mp (hs.fitp_left hval).1
    rw [node_zorg hp x0 (by simp)]
    omega
  | cons8 h f1 f2 f3 pl' =>
    obtain ⟨h8, htop⟩ := hqa
    have hq : qa.toNat = 8 := htop
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons8 h f1 f2 f3 pl').drop 1))) = 8 :=
      (PRange.mem_pr88 _).mp (hs.fitp_left hval).1
    rw [node_zorg hp x0 (by simp)]
    omega

/-- Popping the hat of the left sector. -/
theorem redPoplHat_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.hat qa)
    (hred : redPoplHat redRec ahub p0r pl pr = true) :
    G.arity (G.edge (G.face^[2] (G.node (G.zorg x0 pl)))) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' =>
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.updateHat s) hval.shiftLeft hqa hred
  | cons6 h f1 pl' =>
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update6Hat f1) hval.shiftLeft hqa hred
  | cons7 h f1 f2 pl' =>
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update7Hat f1 f2) hval.shiftLeft hqa hred
  | cons8 h f1 f2 f3 pl' =>
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update8Hat f1 f2 f3) hval.shiftLeft hqa hred

/-- Popping the first counterclockwise fan of the left sector. -/
theorem redPoplFan1R_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.fan1R qa)
    (hred : redPoplFan1R redRec ahub p0r pl pr = true) :
    G.arity (G.zmove .fan1r (G.zorg x0 pl)) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons6 h f1 pl' =>
    simp only [Hypermap.zmove]
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update6Fan1 h) hval.shiftLeft hqa hred
  | cons7 h f1 f2 pl' =>
    simp only [Hypermap.zmove]
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update7Fan1 h f2) hval.shiftLeft hqa hred
  | cons8 h f1 f2 f3 pl' =>
    simp only [Hypermap.zmove]
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update8Fan1 h f2 f3) hval.shiftLeft hqa hred

/-- Popping the second counterclockwise fan of the left sector. -/
theorem redPoplFan2R_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.fan2R qa)
    (hred : redPoplFan2R redRec ahub p0r pl pr = true) :
    G.arity (G.zmove .fan2r (G.zorg x0 pl)) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons6 h f1 pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons7 h f1 f2 pl' =>
    simp only [Hypermap.zmove]
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update7Fan2 h f1) hval.shiftLeft hqa hred
  | cons8 h f1 f2 f3 pl' =>
    simp only [Hypermap.zmove]
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update8Fan2 h f1 f3) hval.shiftLeft hqa hred

/-- Popping the third counterclockwise fan of the left sector. -/
theorem redPoplFan3R_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.fan3R qa)
    (hred : redPoplFan3R redRec ahub p0r pl pr = true) :
    G.arity (G.zmove .fan3r (G.zorg x0 pl)) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons6 h f1 pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons7 h f1 f2 pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons8 h f1 f2 f3 pl' =>
    simp only [Hypermap.zmove]
    rw [node_zorg hp x0 (by simp)]
    exact redPcons_fit hs hrec (G.update8Fan3 h f1 f2) hval.shiftLeft hqa hred

/-- Popping the first clockwise fan of the left sector. -/
theorem redPoplFan1L_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.fan1L qa)
    (hred : redPoplFan1L redRec ahub p0r pl pr = true) :
    G.arity (G.zmove .fan1l (G.zorg x0 pl)) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons6 h f1 pl' =>
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons6 h f1 pl').drop 1))) = 3 + 3 :=
      (PRange.mem_pr66 _).mp (hs.fitp_left hval).1
    rw [arity_zmove_fanl_zorg hp (by simp) hk rfl]
    exact redPcons_fit hs hrec (G.update6Fan1 h) hval.shiftLeft hqa hred
  | cons7 h f1 f2 pl' =>
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons7 h f1 f2 pl').drop 1))) = 3 + 4 :=
      (PRange.mem_pr77 _).mp (hs.fitp_left hval).1
    rw [arity_zmove_fanl_zorg hp (by simp) hk rfl]
    exact redPcons_fit hs hrec (G.update7Fan2 h f1) hval.shiftLeft hqa hred
  | cons8 h f1 f2 f3 pl' =>
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons8 h f1 f2 f3 pl').drop 1))) = 3 + 5 :=
      (PRange.mem_pr88 _).mp (hs.fitp_left hval).1
    rw [arity_zmove_fanl_zorg hp (by simp) hk rfl]
    exact redPcons_fit hs hrec (G.update8Fan3 h f1 f2) hval.shiftLeft hqa hred

/-- Popping the second clockwise fan of the left sector. -/
theorem redPoplFan2L_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.fan2L qa)
    (hred : redPoplFan2L redRec ahub p0r pl pr = true) :
    G.arity (G.zmove .fan2l (G.zorg x0 pl)) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons6 h f1 pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons7 h f1 f2 pl' =>
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons7 h f1 f2 pl').drop 1))) = 4 + 3 :=
      (PRange.mem_pr77 _).mp (hs.fitp_left hval).1
    rw [arity_zmove_fanl_zorg hp (by simp) hk rfl]
    exact redPcons_fit hs hrec (G.update7Fan1 h f2) hval.shiftLeft hqa hred
  | cons8 h f1 f2 f3 pl' =>
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons8 h f1 f2 f3 pl').drop 1))) = 4 + 4 :=
      (PRange.mem_pr88 _).mp (hs.fitp_left hval).1
    rw [arity_zmove_fanl_zorg hp (by simp) hk rfl]
    exact redPcons_fit hs hrec (G.update8Fan2 h f1 f3) hval.shiftLeft hqa hred

/-- Popping the third clockwise fan of the left sector. -/
theorem redPoplFan3L_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {pl pr : Part} (hval : Zvalid p0r pl pr) {qa : QArity} (hqa : Fitqa pl.fan3L qa)
    (hred : redPoplFan3L redRec ahub p0r pl pr = true) :
    G.arity (G.zmove .fan3l (G.zorg x0 pl)) = qa.toNat := by
  have hp := hs.plain
  cases pl with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons s h pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons6 h f1 pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons7 h f1 f2 pl' => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | cons8 h f1 f2 f3 pl' =>
    have hk : G.arity (G.edge (G.zorg x0 ((Part.cons8 h f1 f2 f3 pl').drop 1))) = 5 + 3 :=
      (PRange.mem_pr88 _).mp (hs.fitp_left hval).1
    rw [arity_zmove_fanl_zorg hp (by simp) hk rfl]
    exact redPcons_fit hs hrec (G.update8Fan1 h f2 f3) hval.shiftLeft hqa hred

/-- If the range at the zipper dart matched a qarity and the popped part is
rejected by the recursive check, then the zipper dart has that arity. -/
theorem redPop_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {zp : Zpart} (hval : zp.Valid p0r) {qa : QArity} (hqa : Fitqa (zrange ahub zp) qa)
    (hred : redPop redRec ahub p0r zp = true) : G.arity (G.zdart x0 zp) = qa.toNat := by
  obtain ⟨zi, pl, pr⟩ := zp
  have hp := hs.plain
  have hc := hs.cubic
  have hv : Zvalid p0r pl pr := hval
  cases zi with
  | nil => obtain ⟨h8, htop⟩ := hqa; have h9 : qa.toNat = 9 := htop; omega
  | hub =>
    obtain ⟨h8, htop⟩ := hqa
    change G.arity (G.zorg x0 pl) = qa.toNat
    rw [arity_zorg hs]
    revert h8 htop
    cases ahub <;> simp only [zrange, hubRange, topqa, QArity.toNat] <;> omega
  | hubl => exact redPoplSpoke_fit hs hrec hv hqa hred
  | hubr =>
    rw [show G.zdart x0 ⟨.hubr, pl, pr⟩ = G.zmove .hubr (G.zorg x0 pl) from rfl,
      arity_zmove_hubr hc]
    exact redPoprSpoke_fit hs hrec hv hqa hred
  | hat =>
    rw [show G.zdart x0 ⟨.hat, pl, pr⟩ = G.zmove .hat (G.zorg x0 pl) from rfl,
      arity_zmove_hat hp hc]
    exact redPoprHat_fit hs hrec hv hqa hred
  | hatl =>
    rw [show G.zdart x0 ⟨.hatl, pl, pr⟩ = G.zmove .hatl (G.zorg x0 pl) from rfl,
      arity_zmove_hatl]
    exact redPoplSpoke_fit hs hrec hv hqa hred
  | hatr =>
    rw [show G.zdart x0 ⟨.hatr, pl, pr⟩ = G.zmove .hatr (G.zorg x0 pl) from rfl,
      arity_zmove_hatr hc]
    exact redPoprSpoke_fit hs hrec hv hqa hred
  | fan0l =>
    rw [show G.zdart x0 ⟨.fan0l, pl, pr⟩ = G.zmove .fan0l (G.zorg x0 pl) from rfl,
      arity_zmove_fan0l hp hc]
    exact redPoprHat_fit hs hrec hv hqa hred
  | fan0r => exact redPoplHat_fit hs hrec hv hqa hred
  | fan1l => exact redPoplFan1L_fit hs hrec hv hqa hred
  | fan2l => exact redPoplFan2L_fit hs hrec hv hqa hred
  | fan3l => exact redPoplFan3L_fit hs hrec hv hqa hred
  | fan1r => exact redPoplFan1R_fit hs hrec hv hqa hred
  | fan2r => exact redPoplFan2R_fit hs hrec hv hqa hred
  | fan3r => exact redPoplFan3R_fit hs hrec hv hqa hred

end Hypermap

/-! ### Matching a question against the part -/

/-- The arities the question `q` asks for, on a traversal starting at the
zipper dart, are the tops of the corresponding ranges of the zipper. -/
def Fitqzp (ahub : QArity) (p0l p0r : Part) : Zpart → Question → Prop
  | _, .ask0 => True
  | zp, .ask1 qa => Fitqa (zrange ahub zp) qa
  | zp, .askL qa ql =>
      Fitqa (zrange ahub zp) qa ∧ Fitqzp ahub p0l p0r (zstepLt p0l p0r zp) ql
  | zp, .askR qa qr =>
      Fitqa (zrange ahub zp) qa ∧ Fitqzp ahub p0l p0r (zstepRt p0l p0r zp) qr
  | zp, .askLR qa ql qr =>
      Fitqa (zrange ahub zp) qa ∧ Fitqzp ahub p0l p0r (zstepL p0l p0r zp) ql ∧
        Fitqzp ahub p0l p0r (zstepR p0l p0r zp) qr
  | zp, .askLL qa ql =>
      Fitqa (zrange ahub (zstepL p0l p0r zp)) qa ∧
        Fitqzp ahub p0l p0r (zstepL p0l p0r (zstepL p0l p0r zp)) ql
  | zp, .askRR qa qr =>
      Fitqa (zrange ahub (zstepR p0l p0r zp)) qa ∧
        Fitqzp ahub p0l p0r (zstepR p0l p0r (zstepR p0l p0r zp)) qr

instance decidableFitqzp (ahub : QArity) (p0l p0r : Part) :
    ∀ (zp : Zpart) (q : Question), Decidable (Fitqzp ahub p0l p0r zp q)
  | _, .ask0 => isTrue trivial
  | zp, .ask1 qa => inferInstanceAs (Decidable (Fitqa (zrange ahub zp) qa))
  | zp, .askL _ ql =>
      @instDecidableAnd _ _ inferInstance (decidableFitqzp ahub p0l p0r (zstepLt p0l p0r zp) ql)
  | zp, .askR _ qr =>
      @instDecidableAnd _ _ inferInstance (decidableFitqzp ahub p0l p0r (zstepRt p0l p0r zp) qr)
  | zp, .askLR _ ql qr =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ (decidableFitqzp ahub p0l p0r (zstepL p0l p0r zp) ql)
          (decidableFitqzp ahub p0l p0r (zstepR p0l p0r zp) qr))
  | zp, .askLL _ ql =>
      @instDecidableAnd _ _ inferInstance
        (decidableFitqzp ahub p0l p0r (zstepL p0l p0r (zstepL p0l p0r zp)) ql)
  | zp, .askRR _ qr =>
      @instDecidableAnd _ _ inferInstance
        (decidableFitqzp ahub p0l p0r (zstepR p0l p0r (zstepR p0l p0r zp)) qr)

/-- The recursive check on every range the traversal of `q` tests. -/
def redPopqzp (redRec : Part → Bool) (ahub : QArity) (p0l p0r : Part) :
    Zpart → Question → Bool
  | _, .ask0 => true
  | zp, .ask1 _ => redPop redRec ahub p0r zp
  | zp, .askL _ ql =>
      redPop redRec ahub p0r zp && redPopqzp redRec ahub p0l p0r (zstepLt p0l p0r zp) ql
  | zp, .askR _ qr =>
      redPop redRec ahub p0r zp && redPopqzp redRec ahub p0l p0r (zstepRt p0l p0r zp) qr
  | zp, .askLR _ ql qr =>
      redPop redRec ahub p0r zp && redPopqzp redRec ahub p0l p0r (zstepL p0l p0r zp) ql &&
        redPopqzp redRec ahub p0l p0r (zstepR p0l p0r zp) qr
  | zp, .askLL _ ql =>
      redPop redRec ahub p0r (zstepL p0l p0r zp) &&
        redPopqzp redRec ahub p0l p0r (zstepL p0l p0r (zstepL p0l p0r zp)) ql
  | zp, .askRR _ qr =>
      redPop redRec ahub p0r (zstepR p0l p0r zp) &&
        redPopqzp redRec ahub p0l p0r (zstepR p0l p0r (zstepR p0l p0r zp)) qr

/-- A question that matches a zipper is trivial or the zipper is proper. -/
theorem proper_of_fitqzp {ahub : QArity} {p0l p0r : Part} {zp : Zpart} {q : Question}
    (h : Fitqzp ahub p0l p0r zp q) : q = .ask0 ∨ zp.Proper := by
  cases q with
  | ask0 => exact Or.inl rfl
  | ask1 qa => exact Or.inr (proper_of_fitqa h)
  | askL qa ql => exact Or.inr (proper_of_fitqa h.1)
  | askR qa qr => exact Or.inr (proper_of_fitqa h.1)
  | askLR qa ql qr => exact Or.inr (proper_of_fitqa h.1)
  | askLL qa ql => exact Or.inr (proper_of_proper_stepL (proper_of_fitqa h.1))
  | askRR qa qr => exact Or.inr (proper_of_proper_stepR (proper_of_fitqa h.1))

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}
variable {redRec : Part → Bool}

omit [Finite D] in
/-- The trivial question fits everywhere. -/
@[simp] theorem fitq_ask0 (x : D) : G.Fitq x .ask0 := rfl

omit [Finite D] in
/-- A one-arity question fits when the arity is right. -/
theorem fitq_ask1 (x : D) (qa : QArity) : G.Fitq x (.ask1 qa) ↔ qa.toNat = G.arity x := by
  simp [Fitq, Question.flat, walkq]

omit [Finite D] in
/-- A left question fits when the arity is right and the rest fits after the
left move. -/
theorem fitq_askL (x : D) (qa : QArity) (q : Question) :
    G.Fitq x (.askL qa q) ↔ qa.toNat = G.arity x ∧ G.Fitq (G.qstepL x) q := by
  simp [Fitq, Question.flat, walkq]

omit [Finite D] in
/-- A doubled left question fits when the arity is right and the rest fits
after the two left moves. -/
theorem fitq_askLL (x : D) (qa : QArity) (q : Question) :
    G.Fitq x (.askLL qa q) ↔
      qa.toNat = G.arity (G.edge (G.node (G.qstepL x))) ∧ G.Fitq (G.qstepL (G.qstepL x)) q := by
  simp [Fitq, Question.flat, walkq]

omit [Finite D] in
/-- A doubled right question fits when the arity is right and the rest fits
after the two right moves. -/
theorem fitq_askRR (x : D) (qa : QArity) (q : Question) :
    G.Fitq x (.askRR qa q) ↔
      qa.toNat = G.arity (G.qstepR x) ∧ G.Fitq (G.qstepR (G.qstepR x)) q := by
  simp [Fitq, Question.flat, walkq]

/-- If a question matches the tops of the ranges of a valid zipper and the
recursive check rejects all the popped parts, then the question really fits at
the zipper dart. -/
theorem fitqzp_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub) :
    ∀ (q : Question) (zp : Zpart), Fitqzp ahub p0l p0r zp q →
      redPopqzp redRec ahub p0l p0r zp q = true → zp.Valid p0r → G.Fitq (G.zdart x0 zp) q := by
  intro q
  induction q with
  | ask0 => intro zp _ _ _; exact fitq_ask0 _
  | ask1 qa =>
    intro zp hq hred hval
    rw [fitq_ask1]
    exact (redPop_fit hs hrec hval hq hred).symm
  | askL qa ql ih =>
    intro zp hq hred hval
    obtain ⟨hqa, hql⟩ := hq
    simp only [redPopqzp, Bool.and_eq_true] at hred
    have Dqa : G.arity (G.zdart x0 zp) = qa.toNat := redPop_fit hs hrec hval hqa hred.1
    rw [fitq_askL]
    refine ⟨Dqa.symm, ?_⟩
    rcases proper_of_fitqzp hql with rfl | hprop
    · exact fitq_ask0 _
    · have htop : G.ZpfitTop ahub x0 zp := Dqa.trans hqa.2
      rw [← zdart_stepLt hs htop hval hprop]
      exact ih _ hql hred.2 (valid_stepLt hs hval)
  | askR qa qr ih =>
    intro zp hq hred hval
    obtain ⟨hqa, hqr⟩ := hq
    simp only [redPopqzp, Bool.and_eq_true] at hred
    have Dqa : G.arity (G.zdart x0 zp) = qa.toNat := redPop_fit hs hrec hval hqa hred.1
    rw [G.fitq_askR]
    refine ⟨Dqa.symm, ?_⟩
    rcases proper_of_fitqzp hqr with rfl | hprop
    · exact fitq_ask0 _
    · have htop : G.ZpfitTop ahub x0 zp := Dqa.trans hqa.2
      rw [← zdart_stepRt hs htop hval hprop]
      exact ih _ hqr hred.2 (valid_stepRt hs hval)
  | askLR qa ql qr ihl ihr =>
    intro zp hq hred hval
    obtain ⟨hqa, hql, hqr⟩ := hq
    simp only [redPopqzp, Bool.and_eq_true] at hred
    obtain ⟨⟨hredp, hredl⟩, hredr⟩ := hred
    have Dqa : G.arity (G.zdart x0 zp) = qa.toNat := redPop_fit hs hrec hval hqa hredp
    rw [G.fitq_askLR]
    refine ⟨Dqa.symm, ?_, ?_⟩
    · rcases proper_of_fitqzp hql with rfl | hprop
      · exact fitq_ask0 _
      · rw [← zdart_stepL hs hval hprop]
        exact ihl _ hql hredl (valid_stepL hs hval)
    · rcases proper_of_fitqzp hqr with rfl | hprop
      · exact fitq_ask0 _
      · rw [← zdart_stepR hs hval hprop]
        exact ihr _ hqr hredr (valid_stepR hs hval)
  | askLL qa ql ih =>
    intro zp hq hred hval
    obtain ⟨hqa, hql⟩ := hq
    simp only [redPopqzp, Bool.and_eq_true] at hred
    have hprop1 : (zstepL p0l p0r zp).Proper := proper_of_fitqa hqa
    have hval1 : (zstepL p0l p0r zp).Valid p0r := valid_stepL hs hval
    have hd1 : G.zdart x0 (zstepL p0l p0r zp) = G.qstepL (G.zdart x0 zp) :=
      zdart_stepL hs hval hprop1
    have Dqa : G.arity (G.zdart x0 (zstepL p0l p0r zp)) = qa.toNat :=
      redPop_fit hs hrec hval1 hqa hred.1
    rw [fitq_askLL]
    constructor
    · rw [show G.arity (G.edge (G.node (G.qstepL (G.zdart x0 zp))))
            = G.arity (G.qstepL (G.zdart x0 zp)) from G.arity_facePred _, ← hd1, Dqa]
    · rw [← hd1]
      rcases proper_of_fitqzp hql with rfl | hprop
      · exact fitq_ask0 _
      · rw [← zdart_stepL hs hval1 hprop]
        exact ih _ hql hred.2 (valid_stepL hs hval1)
  | askRR qa qr ih =>
    intro zp hq hred hval
    obtain ⟨hqa, hqr⟩ := hq
    simp only [redPopqzp, Bool.and_eq_true] at hred
    have hprop1 : (zstepR p0l p0r zp).Proper := proper_of_fitqa hqa
    have hval1 : (zstepR p0l p0r zp).Valid p0r := valid_stepR hs hval
    have hd1 : G.zdart x0 (zstepR p0l p0r zp) = G.qstepR (G.zdart x0 zp) :=
      zdart_stepR hs hval hprop1
    have Dqa : G.arity (G.zdart x0 (zstepR p0l p0r zp)) = qa.toNat :=
      redPop_fit hs hrec hval1 hqa hred.1
    rw [fitq_askRR]
    constructor
    · rw [← hd1, Dqa]
    · rw [← hd1]
      rcases proper_of_fitqzp hqr with rfl | hprop
      · exact fitq_ask0 _
      · rw [← zdart_stepR hs hval1 hprop]
        exact ih _ hqr hred.2 (valid_stepR hs hval1)

end Hypermap

/-! ### Matching the quizzes stored at a node -/

/-- Scan a leaf list of the quiz tree for a triple of questions that matches
the three zippers and whose popped parts are all rejected. -/
def redQztLeaf (redRec : Part → Bool) (ahub : QArity) (p0l p0r : Part)
    (zp1 zp2 zp3 : Zpart) : QuizTree → Bool
  | .leaf q1 q2 q3 t =>
      if Fitqzp ahub p0l p0r zp3 q3 ∧ Fitqzp ahub p0l p0r zp2 q2 ∧
          Fitqzp ahub p0l p0r zp1 q1 then
        redPopqzp redRec ahub p0l p0r zp1 q1 && redPopqzp redRec ahub p0l p0r zp2 q2 &&
          redPopqzp redRec ahub p0l p0r zp3 q3
      else redQztLeaf redRec ahub p0l p0r zp1 zp2 zp3 t
  | _ => false

/-- The branch of a quiz tree indexed by the top of an arity range. -/
def qztGetr (r : PRange) (t : QuizTree) : QuizTree :=
  match t with
  | .node t5 t6 t7 t8 =>
      match r with
      | .pr55 => t5
      | .pr56 | .pr66 => t6
      | .pr57 | .pr67 | .pr77 => t7
      | .pr58 | .pr68 | .pr78 | .pr88 => t8
      | _ => .nil
  | _ => .nil

/-- A nonempty branch is reached by the top of the range, which is then at most
eight. -/
theorem qztGetr_fit {r : PRange} {t : QuizTree} (h : (qztGetr r t).Proper) :
    Fitqa r (topqa r) ∧ QuizTree.get1 (topqa r) t = qztGetr r t ∧ t.Proper := by
  cases t with
  | nil => exact h.elim
  | leaf _ _ _ _ => exact h.elim
  | hubNode _ _ _ _ => exact h.elim
  | node t5 t6 t7 t8 =>
    cases r <;> first | exact h.elim | exact ⟨⟨by decide, rfl⟩, rfl, trivial⟩

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}
variable {redRec : Part → Bool}

/-- If a leaf list of the quiz tree matches the three zippers, then it really
fits at every dart whose node the three zippers describe. -/
theorem redQztLeaf_fit (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {zp1 zp2 zp3 : Zpart} (hv1 : zp1.Valid p0r) (hv2 : zp2.Valid p0r) (hv3 : zp3.Valid p0r) :
    ∀ t : QuizTree, redQztLeaf redRec ahub p0l p0r zp1 zp2 zp3 t = true →
      t.Proper ∧ ∀ x : D, G.Zpfit x0 (G.qstepR x) zp1 →
        G.Zpfit x0 (G.qstepR (G.node x)) zp2 →
        G.Zpfit x0 (G.qstepR (G.node (G.node x))) zp3 → G.Fitl x t := by
  intro t
  induction t with
  | nil => intro h; exact absurd h (by simp [redQztLeaf])
  | node _ _ _ _ _ _ _ _ => intro h; exact absurd h (by simp [redQztLeaf])
  | hubNode _ _ _ _ _ _ _ _ => intro h; exact absurd h (by simp [redQztLeaf])
  | leaf q1 q2 q3 t ih =>
    intro h
    refine ⟨trivial, ?_⟩
    intro x hf1 hf2 hf3
    rw [redQztLeaf] at h
    split at h
    · rename_i hfit
      obtain ⟨hq3, hq2, hq1⟩ := hfit
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hr1, hr2⟩, hr3⟩ := h
      refine Or.inl ⟨?_, ?_, ?_⟩
      · rcases proper_of_fitqzp hq1 with rfl | hpr
        · exact fitq_ask0 _
        · rw [← hf1 hpr]; exact fitqzp_fit hs hrec _ _ hq1 hr1 hv1
      · rcases proper_of_fitqzp hq2 with rfl | hpr
        · exact fitq_ask0 _
        · rw [← hf2 hpr]; exact fitqzp_fit hs hrec _ _ hq2 hr2 hv2
      · rcases proper_of_fitqzp hq3 with rfl | hpr
        · exact fitq_ask0 _
        · rw [← hf3 hpr]; exact fitqzp_fit hs hrec _ _ hq3 hr3 hv3
    · exact Or.inr ((ih h).2 x hf1 hf2 hf3)

omit [Finite D] in
/-- Under the standing assumption that the quiz tree fits nowhere, no leaf list
indexed by the arities around a node can fit at that node. -/
theorem not_fitl_get3 {qt : QuizTree} (hqt : ∀ y : D, ¬ G.Fit y qt) (y : D)
    {qa1 qa2 qa3 : QArity} (h1 : G.arity y = qa1.toNat) (h2 : G.arity (G.node y) = qa2.toNat)
    (h3 : G.arity (G.node (G.node y)) = qa3.toNat) :
    ¬ G.Fitl y (QuizTree.get3 qa1 qa2 qa3 qt) := by
  have e1 : G.qarity y = qa1 := by
    change QArity.ofArity (G.arity y) = qa1
    rw [h1, QArity.ofArity_toNat]
  have e2 : G.qarity (G.node y) = qa2 := by
    change QArity.ofArity (G.arity (G.node y)) = qa2
    rw [h2, QArity.ofArity_toNat]
  have e3 : G.qarity (G.node (G.node y)) = qa3 := by
    change QArity.ofArity (G.arity (G.node (G.node y))) = qa3
    rw [h3, QArity.ofArity_toNat]
  intro hfitl
  refine hqt y ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [e1, h1]
  · rw [e2, h2]
  · rw [e3, h3]
  · rw [e1, e2, e3]; exact hfitl

omit [Finite D] in
/-- A node step is a backward face step followed by an edge step. -/
theorem node_iterate_face (hp : G.Plain) (t : D) {i j : ℕ} (hij : i = j + 1) :
    G.node (G.face^[i] t) = G.edge (G.face^[j] t) := by
  subst hij
  rw [Function.iterate_succ_apply' (G.face : D → D) j t, hp.node_face]

/-- The second dart of a node lies on the same face as the edge dart. -/
theorem arity_node_node_iterate (hp : G.Plain) (hc : G.Cubic) (t : D) {i j : ℕ}
    (hij : i = j + 1) :
    G.arity (G.node (G.node (G.face^[i] t))) = G.arity (G.edge (G.face^[i] t)) := by
  subst hij
  rw [node_iterate_face hp t rfl, node_edge hp hc, G.arity_face,
    ← Function.iterate_succ_apply' (G.face : D → D) j t]

omit [Finite D] in
/-- A right quiz step moves one dart forward around a face. -/
theorem qstepR_iterate (hp : G.Plain) (hc : G.Cubic) (t : D) {i j : ℕ} (hij : j = i + 1) :
    G.qstepR (G.face^[i] t) = G.face (G.edge (G.face^[j] t)) := by
  subst hij
  rw [Function.iterate_succ_apply' (G.face : D → D) i t]
  exact node_edge hp hc _

omit [Finite D] in
/-- A right quiz step from the node of a dart two steps along a face. -/
theorem qstepR_node_iterate (hp : G.Plain) (t : D) {i j : ℕ} (hij : i = j + 2) :
    G.qstepR (G.node (G.face^[i] t)) = G.edge (G.face^[j] t) := by
  subst hij
  rw [show j + 2 = (j + 1) + 1 from rfl, Function.iterate_succ_apply' (G.face : D → D) (j + 1) t]
  change G.node (G.edge (G.node (G.face (G.face^[j + 1] t)))) = _
  rw [hp.node_face, hp.edge_edge, Function.iterate_succ_apply' (G.face : D → D) j t,
    hp.node_face]

omit [Finite D] in
/-- A dart in the left fan chain at the next subpart, given the spoke arity. -/
theorem zmove_fanl_face (hp : G.Plain) {zi : ZpartLoc} (u : D) {j m : ℕ}
    (hk : G.arity (G.edge u) = j + m)
    (hz : G.zmove zi (G.face u) = G.face (G.edge (G.facePred^[j] (G.node (G.face u))))) :
    G.zmove zi (G.face u) = G.face (G.edge (G.face^[m] (G.edge u))) := by
  rw [hz, hp.node_face, facePred_iterate_add hk]

omit [Finite D] in
/-- A dart in the right fan chain at the next subpart. -/
theorem zmove_fanr_face (hp : G.Plain) {zi : ZpartLoc} (u : D) {j : ℕ}
    (hz : G.zmove zi (G.face u) = G.edge (G.face^[j] (G.node (G.face u)))) :
    G.zmove zi (G.face u) = G.edge (G.face^[j] (G.edge u)) := by
  rw [hz, hp.node_face]

omit [Finite D] in
/-- The `hatr` dart at the next subpart, given the spoke arity. -/
theorem zmove_hatr_face (hp : G.Plain) (hc : G.Cubic) (u : D) {m : ℕ}
    (hk : G.arity (G.edge u) = 1 + m) :
    G.zmove .hatr (G.face u) = G.face (G.edge (G.face^[m] (G.edge u))) := by
  rw [← facePred_iterate_add hk, Function.iterate_one, ← node_eq_edge_facePred hp]
  zsimp hp, hc

omit [Finite D] in
/-- The `hatl` dart, in closed form. -/
theorem zmove_hatl_eq (hc : G.Cubic) (u : D) :
    G.zmove .hatl u = G.edge (G.face^[1] (G.edge u)) := by
  change G.edge (G.node (G.node u)) = _
  rw [hc.node_node, Function.iterate_one]

omit [Finite D] in
/-- Shifting the zipper right moves the origin one face step forward. -/
theorem zorg_shift (x0 : D) {pr : Part} (hpr : pr ≠ .nil) (pl : Part) :
    G.zorg x0 (Part.shift pr pl) = G.face (G.zorg x0 pl) := by
  change G.face^[(Part.shift pr pl).size] x0 = G.face (G.face^[pl.size] x0)
  rw [Part.size_shift_of_ne_nil hpr, Function.iterate_succ_apply']

end Hypermap

namespace Part

/-- Shifting does not change the first counterclockwise fan range. -/
theorem fan1R_shift {p : Part} (h : p ≠ .nil) (q : Part) : (shift p q).fan1R = p.fan1R := by
  cases p with
  | nil => exact absurd rfl h
  | cons => rfl
  | cons6 => rfl
  | cons7 => rfl
  | cons8 => rfl

/-- Shifting does not change the second counterclockwise fan range. -/
theorem fan2R_shift {p : Part} (h : p ≠ .nil) (q : Part) : (shift p q).fan2R = p.fan2R := by
  cases p with
  | nil => exact absurd rfl h
  | cons => rfl
  | cons6 => rfl
  | cons7 => rfl
  | cons8 => rfl

/-- Shifting does not change the third counterclockwise fan range. -/
theorem fan3R_shift {p : Part} (h : p ≠ .nil) (q : Part) : (shift p q).fan3R = p.fan3R := by
  cases p with
  | nil => exact absurd rfl h
  | cons => rfl
  | cons6 => rfl
  | cons7 => rfl
  | cons8 => rfl

end Part

/-! ### The reducibility check on a part

`redZpartRec` walks the part, testing at each subpart whether one of the
quizzes stored in the tree matches the tops of the ranges at the node just
outside the hub, and whether the recursive check rejects every part obtained by
popping one of the matched ranges. -/

/-- The tests that use a fan of the current subpart, according to the shape of
the right sector. -/
def redZpartFan (redRec : Part → Bool) (ahub : QArity) (p0l p0r : Part) (sqt : QuizTree)
    (pl pr pl1 pr1 : Part) : Bool :=
  match pr with
  | .cons .pr55 hh _ =>
      if redQztLeaf redRec ahub p0l p0r ⟨.hatr, pl1, pr1⟩ ⟨.hatl, pl, pr⟩ ⟨.nil, pl1, pr1⟩
          (qztGetr pr1.hat (qztGetr hh sqt)) then
        redPoprHat redRec ahub p0r pr1 && redPoprHat redRec ahub p0r pr
      else false
  | .cons6 hh f1 _ =>
      if redQztLeaf redRec ahub p0l p0r ⟨.fan0l, pl1, pr1⟩ ⟨.hatl, pl, pr⟩ ⟨.nil, pl1, pr1⟩
          (qztGetr f1 (qztGetr hh sqt)) then
        redPoplFan1R redRec ahub p0r pl1 pr1 && redPoprHat redRec ahub p0r pr
      else if redQztLeaf redRec ahub p0l p0r ⟨.hatr, pl1, pr1⟩ ⟨.fan0r, pl1, pr1⟩
          ⟨.nil, pl1, pr1⟩ (qztGetr pr1.hat (qztGetr f1 sqt)) then
        redPoprHat redRec ahub p0r pr1 && redPoplFan1R redRec ahub p0r pl1 pr1
      else false
  | .cons7 hh f1 f2 _ =>
      if redQztLeaf redRec ahub p0l p0r ⟨.fan1l, pl1, pr1⟩ ⟨.hatl, pl, pr⟩ ⟨.nil, pl1, pr1⟩
          (qztGetr f1 (qztGetr hh sqt)) then
        redPoplFan1R redRec ahub p0r pl1 pr1 && redPoprHat redRec ahub p0r pr
      else if redQztLeaf redRec ahub p0l p0r ⟨.fan0l, pl1, pr1⟩ ⟨.fan0r, pl1, pr1⟩
          ⟨.nil, pl1, pr1⟩ (qztGetr f2 (qztGetr f1 sqt)) then
        redPoplFan2R redRec ahub p0r pl1 pr1 && redPoplFan1R redRec ahub p0r pl1 pr1
      else if redQztLeaf redRec ahub p0l p0r ⟨.hatr, pl1, pr1⟩ ⟨.fan1r, pl1, pr1⟩
          ⟨.nil, pl1, pr1⟩ (qztGetr pr1.hat (qztGetr f2 sqt)) then
        redPoprHat redRec ahub p0r pr1 && redPoplFan2R redRec ahub p0r pl1 pr1
      else false
  | .cons8 hh f1 f2 f3 _ =>
      if redQztLeaf redRec ahub p0l p0r ⟨.fan2l, pl1, pr1⟩ ⟨.hatl, pl, pr⟩ ⟨.nil, pl1, pr1⟩
          (qztGetr f1 (qztGetr hh sqt)) then
        redPoplFan1R redRec ahub p0r pl1 pr1 && redPoprHat redRec ahub p0r pr
      else if redQztLeaf redRec ahub p0l p0r ⟨.fan1l, pl1, pr1⟩ ⟨.fan0r, pl1, pr1⟩
          ⟨.nil, pl1, pr1⟩ (qztGetr f2 (qztGetr f1 sqt)) then
        redPoplFan2R redRec ahub p0r pl1 pr1 && redPoplFan1R redRec ahub p0r pl1 pr1
      else if redQztLeaf redRec ahub p0l p0r ⟨.fan0l, pl1, pr1⟩ ⟨.fan1r, pl1, pr1⟩
          ⟨.nil, pl1, pr1⟩ (qztGetr f3 (qztGetr f2 sqt)) then
        redPoplFan3R redRec ahub p0r pl1 pr1 && redPoplFan2R redRec ahub p0r pl1 pr1
      else if redQztLeaf redRec ahub p0l p0r ⟨.hatr, pl1, pr1⟩ ⟨.fan2r, pl1, pr1⟩
          ⟨.nil, pl1, pr1⟩ (qztGetr pr1.hat (qztGetr f3 sqt)) then
        redPoprHat redRec ahub p0r pr1 && redPoplFan3R redRec ahub p0r pl1 pr1
      else false
  | _ => false

/-- One step of the reducibility walk, at the subpart between the sectors `pl`
and `pr`. -/
def redZpartStep (redRec : Part → Bool) (ahub : QArity) (p0l p0r : Part) (qt : QuizTree)
    (pl pr : Part) : Bool :=
  if (qztGetr pr.spoke (QuizTree.truncate qt)).Proper then
    if redQztLeaf redRec ahub p0l p0r
        ⟨.hubr, Part.shift pr pl, pr.drop 1⟩
        (zshiftl p0l p0r .hubl ⟨.hub, pl, pr⟩)
        ⟨.hat, pl, pr⟩
        (qztGetr pr.spoke (qztGetr pl.spoke (QuizTree.get1 ahub qt))) then
      redPoprSpoke redRec ahub p0r pr && redPoplSpoke redRec ahub p0r pl pr
    else if redQztLeaf redRec ahub p0l p0r
        ⟨zfanLt pr, Part.shift pr pl, pr.drop 1⟩
        ⟨.hub, pl, pr⟩
        ⟨zfanRt pl, pl, pr⟩
        (qztGetr pr.hat (qztGetr pl.spoke (qztGetr pr.spoke (QuizTree.truncate qt)))) then
      redPoprHat redRec ahub p0r pr && redPoplSpoke redRec ahub p0r pl pr &&
        redPoprSpoke redRec ahub p0r pr
    else
      redZpartFan redRec ahub p0l p0r (qztGetr pr.spoke (QuizTree.truncate qt)) pl pr
        (Part.shift pr pl) (pr.drop 1)
  else false

/-- The reducibility walk, for `d` further subparts. -/
def redZpartRec (redRec : Part → Bool) (ahub : QArity) (p0l p0r : Part) (qt : QuizTree) :
    Part → Part → ℕ → Bool
  | _, _, 0 => false
  | pl, pr, d + 1 =>
      redZpartStep redRec ahub p0l p0r qt pl pr ||
        redZpartRec redRec ahub p0l p0r qt (Part.shift pr pl) (pr.drop 1) d

/-- The reducibility walk all the way around the hub. -/
def redZpart (redRec : Part → Bool) (ahub : QArity) (p0l p0r : Part) (qt : QuizTree) : Bool :=
  redZpartRec redRec ahub p0l p0r qt (p0l.drop 1) (Part.shift p0l p0r) ahub.toNat

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D} {ahub : QArity} {p0l p0r : Part} {x0 : D}
variable {redRec : Part → Bool}

/-- The contradiction at the heart of every test: a matching leaf list would
make the quiz tree fit at a node of the map. -/
theorem leaf_absurd (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {qt : QuizTree} (hqt : ∀ y : D, ¬ G.Fit y qt) (y : D) {zp1 zp2 zp3 : Zpart}
    (hv1 : zp1.Valid p0r) (hv2 : zp2.Valid p0r) (hv3 : zp3.Valid p0r)
    (hd1 : G.Zpfit x0 (G.qstepR y) zp1) (hd2 : G.Zpfit x0 (G.qstepR (G.node y)) zp2)
    (hd3 : G.Zpfit x0 (G.qstepR (G.node (G.node y))) zp3)
    {qa1 qa2 qa3 : QArity} (ha1 : G.arity y = qa1.toNat)
    (ha2 : G.arity (G.node y) = qa2.toNat)
    (ha3 : G.arity (G.node (G.node y)) = qa3.toNat)
    {t : QuizTree} (ht : t = QuizTree.get3 qa1 qa2 qa3 qt)
    (hleaf : redQztLeaf redRec ahub p0l p0r zp1 zp2 zp3 t = true) : False := by
  obtain ⟨_, hfit⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 t hleaf
  exact not_fitl_get3 hqt y ha1 ha2 ha3 (ht ▸ hfit y hd1 hd2 hd3)

omit [Finite D] in
/-- An improper zipper part fits vacuously. -/
theorem zpfit_nil (x : D) (pl pr : Part) : G.Zpfit x0 x ⟨.nil, pl, pr⟩ :=
  fun hcon => absurd rfl hcon

/-- No fan test can succeed, under the standing assumptions. -/
theorem not_redZpartFan (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {qt : QuizTree} (hqt : ∀ y : D, ¬ G.Fit y qt) {pl pr pl1 pr1 : Part}
    (hpl1 : pl1 = Part.shift pr pl) (hpr : pr ≠ .nil) (hval : Zvalid p0r pl pr)
    (hval1 : Zvalid p0r pl1 pr1) (hx1 : G.zorg x0 pl1 = G.face (G.zorg x0 pl))
    (hqs : Fitqa pr.spoke (topqa pr.spoke))
    {sqt : QuizTree} (hsqt : sqt = QuizTree.get1 (topqa pr.spoke) qt) :
    redZpartFan redRec ahub p0l p0r sqt pl pr pl1 pr1 = false := by
  have hp := hs.plain
  have hc := hs.cubic
  cases pr with
  | nil => exact absurd rfl hpr
  | cons s hh p =>
    cases s
    case pr55 =>
      have hk := redPoprSpoke_fit hs hrec hval hqs rfl
      rw [redZpartFan]
      split
      · rename_i hleaf
        rw [← Bool.not_eq_true]
        intro hcon
        rw [Bool.and_eq_true] at hcon
        obtain ⟨hredA, hredB⟩ := hcon
        have hv1 : (⟨.hatr, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        have hv2 : (⟨.hatl, pl, (Part.cons PRange.pr55 hh p)⟩ : Zpart).Valid p0r := hval
        have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
        obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
        obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
        have hd1 : G.Zpfit x0 (G.qstepR (G.face^[3] (G.edge (G.zorg x0 pl))))
            ⟨.hatr, pl1, pr1⟩ := by
          intro _
          change G.zmove .hatr (G.zorg x0 pl1) = _
          rw [hx1, zmove_hatr_face hp hc (G.zorg x0 pl)
              (show G.arity (G.edge (G.zorg x0 pl)) = 1 + 4 from hk),
            qstepR_iterate hp hc _ (show (4 : ℕ) = 3 + 1 from rfl)]
        have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
            ⟨.hatl, pl, (Part.cons PRange.pr55 hh p)⟩ := by
          intro _
          change G.zmove .hatl (G.zorg x0 pl) = _
          rw [zmove_hatl_eq hc, qstepR_node_iterate hp _ (show (3 : ℕ) = 1 + 2 from rfl)]
        have ha1 : G.arity (G.face^[3] (G.edge (G.zorg x0 pl))) = QArity.qa5.toNat := by
          rw [G.arity_iterate_face]; exact hk
        have ha2 : G.arity (G.node (G.face^[3] (G.edge (G.zorg x0 pl))))
            = (topqa hh).toNat := by
          rw [node_iterate_face hp _ (show (3 : ℕ) = 2 + 1 from rfl)]
          exact redPoprHat_fit hs hrec hval hq2 hredB
        have ha3 : G.arity (G.node (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
            = (topqa pr1.hat).toNat := by
          rw [arity_node_node_iterate hp hc _ (show (3 : ℕ) = 2 + 1 from rfl)]
          have hprev : G.arity (G.edge (G.face^[2] (G.edge (G.face (G.zorg x0 pl)))))
              = G.arity (G.edge (G.face^[3] (G.edge (G.zorg x0 pl)))) :=
            G.arity_hat_prev hp hc (G.zorg x0 pl)
              (show G.arity (G.edge (G.zorg x0 pl)) = 5 from hk) (by omega)
          rw [← hprev, ← hx1]
          exact redPoprHat_fit hs hrec hval1 hq3 hredA
        have ht : qztGetr pr1.hat (qztGetr hh sqt)
            = QuizTree.get3 QArity.qa5 (topqa hh) (topqa pr1.hat) qt := by
          rw [← hg3, ← hg2, hsqt]
          rfl
        exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
      · rfl
    all_goals rfl
  | cons6 hh f1 p =>
    have hk := redPoprSpoke_fit hs hrec hval hqs rfl
    have hf1 : pl1.fan1R = f1 := by rw [hpl1]; rfl
    rw [redZpartFan]
    split
    · rename_i hleaf
      rw [← Bool.not_eq_true]
      intro hcon
      rw [Bool.and_eq_true] at hcon
      obtain ⟨hredA, hredB⟩ := hcon
      have hv1 : (⟨.fan0l, pl1, pr1⟩ : Zpart).Valid p0r := hval1
      have hv2 : (⟨.hatl, pl, (Part.cons6 hh f1 p)⟩ : Zpart).Valid p0r := hval
      have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
      obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
      obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
      obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
      have hd1 : G.Zpfit x0 (G.qstepR (G.face^[3] (G.edge (G.zorg x0 pl))))
          ⟨.fan0l, pl1, pr1⟩ := by
        intro _
        change G.zmove .fan0l (G.zorg x0 pl1) = _
        rw [hx1, zmove_fanl_face (zi := .fan0l) hp (G.zorg x0 pl)
            (show G.arity (G.edge (G.zorg x0 pl)) = 2 + 4 from hk) rfl,
          qstepR_iterate hp hc _ (show (4 : ℕ) = 3 + 1 from rfl)]
      have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
          ⟨.hatl, pl, (Part.cons6 hh f1 p)⟩ := by
        intro _
        change G.zmove .hatl (G.zorg x0 pl) = _
        rw [zmove_hatl_eq hc, qstepR_node_iterate hp _ (show (3 : ℕ) = 1 + 2 from rfl)]
      have ha1 : G.arity (G.face^[3] (G.edge (G.zorg x0 pl))) = QArity.qa6.toNat := by
        rw [G.arity_iterate_face]; exact hk
      have ha2 : G.arity (G.node (G.face^[3] (G.edge (G.zorg x0 pl))))
          = (topqa hh).toNat := by
        rw [node_iterate_face hp _ (show (3 : ℕ) = 2 + 1 from rfl)]
        exact redPoprHat_fit hs hrec hval hq2 hredB
      have ha3 : G.arity (G.node (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
          = (topqa f1).toNat := by
        rw [arity_node_node_iterate hp hc _ (show (3 : ℕ) = 2 + 1 from rfl)]
        have hfr : G.zmove .fan1r (G.zorg x0 pl1)
            = G.edge (G.face^[3] (G.edge (G.zorg x0 pl))) := by
          rw [hx1]; exact zmove_fanr_face hp _ rfl
        rw [← hfr]
        exact redPoplFan1R_fit hs hrec hval1 (by rw [hf1]; exact hq3) hredA
      have ht : qztGetr f1 (qztGetr hh sqt)
          = QuizTree.get3 QArity.qa6 (topqa hh) (topqa f1) qt := by
        rw [← hg3, ← hg2, hsqt]
        rfl
      exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
    · split
      · rename_i hleaf
        rw [← Bool.not_eq_true]
        intro hcon
        rw [Bool.and_eq_true] at hcon
        obtain ⟨hredA, hredB⟩ := hcon
        have hv1 : (⟨.hatr, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        have hv2 : (⟨.fan0r, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
        obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
        obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
        have hd1 : G.Zpfit x0 (G.qstepR (G.face^[4] (G.edge (G.zorg x0 pl))))
            ⟨.hatr, pl1, pr1⟩ := by
          intro _
          change G.zmove .hatr (G.zorg x0 pl1) = _
          rw [hx1, zmove_hatr_face hp hc (G.zorg x0 pl)
              (show G.arity (G.edge (G.zorg x0 pl)) = 1 + 5 from hk),
            qstepR_iterate hp hc _ (show (5 : ℕ) = 4 + 1 from rfl)]
        have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[4] (G.edge (G.zorg x0 pl)))))
            ⟨.fan0r, pl1, pr1⟩ := by
          intro _
          change G.zmove .fan0r (G.zorg x0 pl1) = _
          rw [hx1, zmove_fanr_face (zi := .fan0r) hp (G.zorg x0 pl) rfl,
            qstepR_node_iterate hp _ (show (4 : ℕ) = 2 + 2 from rfl)]
        have ha1 : G.arity (G.face^[4] (G.edge (G.zorg x0 pl))) = QArity.qa6.toNat := by
          rw [G.arity_iterate_face]; exact hk
        have ha2 : G.arity (G.node (G.face^[4] (G.edge (G.zorg x0 pl))))
            = (topqa f1).toNat := by
          rw [node_iterate_face hp _ (show (4 : ℕ) = 3 + 1 from rfl)]
          have hfr : G.zmove .fan1r (G.zorg x0 pl1)
              = G.edge (G.face^[3] (G.edge (G.zorg x0 pl))) := by
            rw [hx1]; exact zmove_fanr_face hp _ rfl
          rw [← hfr]
          exact redPoplFan1R_fit hs hrec hval1 (by rw [hf1]; exact hq2) hredB
        have ha3 : G.arity (G.node (G.node (G.face^[4] (G.edge (G.zorg x0 pl)))))
            = (topqa pr1.hat).toNat := by
          rw [arity_node_node_iterate hp hc _ (show (4 : ℕ) = 3 + 1 from rfl)]
          have hprev : G.arity (G.edge (G.face^[2] (G.edge (G.face (G.zorg x0 pl)))))
              = G.arity (G.edge (G.face^[4] (G.edge (G.zorg x0 pl)))) :=
            G.arity_hat_prev hp hc (G.zorg x0 pl)
              (show G.arity (G.edge (G.zorg x0 pl)) = 6 from hk) (by omega)
          rw [← hprev, ← hx1]
          exact redPoprHat_fit hs hrec hval1 hq3 hredA
        have ht : qztGetr pr1.hat (qztGetr f1 sqt)
            = QuizTree.get3 QArity.qa6 (topqa f1) (topqa pr1.hat) qt := by
          rw [← hg3, ← hg2, hsqt]
          rfl
        exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
      · rfl
  | cons7 hh f1 f2 p =>
    have hk := redPoprSpoke_fit hs hrec hval hqs rfl
    have hf1 : pl1.fan1R = f1 := by rw [hpl1]; rfl
    have hf2 : pl1.fan2R = f2 := by rw [hpl1]; rfl
    rw [redZpartFan]
    split
    · rename_i hleaf
      rw [← Bool.not_eq_true]
      intro hcon
      rw [Bool.and_eq_true] at hcon
      obtain ⟨hredA, hredB⟩ := hcon
      have hv1 : (⟨.fan1l, pl1, pr1⟩ : Zpart).Valid p0r := hval1
      have hv2 : (⟨.hatl, pl, (Part.cons7 hh f1 f2 p)⟩ : Zpart).Valid p0r := hval
      have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
      obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
      obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
      obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
      have hd1 : G.Zpfit x0 (G.qstepR (G.face^[3] (G.edge (G.zorg x0 pl))))
          ⟨.fan1l, pl1, pr1⟩ := by
        intro _
        change G.zmove .fan1l (G.zorg x0 pl1) = _
        rw [hx1, zmove_fanl_face (zi := .fan1l) hp (G.zorg x0 pl)
            (show G.arity (G.edge (G.zorg x0 pl)) = 3 + 4 from hk) rfl,
          qstepR_iterate hp hc _ (show (4 : ℕ) = 3 + 1 from rfl)]
      have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
          ⟨.hatl, pl, (Part.cons7 hh f1 f2 p)⟩ := by
        intro _
        change G.zmove .hatl (G.zorg x0 pl) = _
        rw [zmove_hatl_eq hc, qstepR_node_iterate hp _ (show (3 : ℕ) = 1 + 2 from rfl)]
      have ha1 : G.arity (G.face^[3] (G.edge (G.zorg x0 pl))) = QArity.qa7.toNat := by
        rw [G.arity_iterate_face]; exact hk
      have ha2 : G.arity (G.node (G.face^[3] (G.edge (G.zorg x0 pl))))
          = (topqa hh).toNat := by
        rw [node_iterate_face hp _ (show (3 : ℕ) = 2 + 1 from rfl)]
        exact redPoprHat_fit hs hrec hval hq2 hredB
      have ha3 : G.arity (G.node (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
          = (topqa f1).toNat := by
        rw [arity_node_node_iterate hp hc _ (show (3 : ℕ) = 2 + 1 from rfl)]
        have hfr : G.zmove .fan1r (G.zorg x0 pl1)
            = G.edge (G.face^[3] (G.edge (G.zorg x0 pl))) := by
          rw [hx1]; exact zmove_fanr_face hp _ rfl
        rw [← hfr]
        exact redPoplFan1R_fit hs hrec hval1 (by rw [hf1]; exact hq3) hredA
      have ht : qztGetr f1 (qztGetr hh sqt)
          = QuizTree.get3 QArity.qa7 (topqa hh) (topqa f1) qt := by
        rw [← hg3, ← hg2, hsqt]
        rfl
      exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
    · split
      · rename_i hleaf
        rw [← Bool.not_eq_true]
        intro hcon
        rw [Bool.and_eq_true] at hcon
        obtain ⟨hredA, hredB⟩ := hcon
        have hv1 : (⟨.fan0l, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        have hv2 : (⟨.fan0r, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
        obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
        obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
        have hd1 : G.Zpfit x0 (G.qstepR (G.face^[4] (G.edge (G.zorg x0 pl))))
            ⟨.fan0l, pl1, pr1⟩ := by
          intro _
          change G.zmove .fan0l (G.zorg x0 pl1) = _
          rw [hx1, zmove_fanl_face (zi := .fan0l) hp (G.zorg x0 pl)
              (show G.arity (G.edge (G.zorg x0 pl)) = 2 + 5 from hk) rfl,
            qstepR_iterate hp hc _ (show (5 : ℕ) = 4 + 1 from rfl)]
        have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[4] (G.edge (G.zorg x0 pl)))))
            ⟨.fan0r, pl1, pr1⟩ := by
          intro _
          change G.zmove .fan0r (G.zorg x0 pl1) = _
          rw [hx1, zmove_fanr_face (zi := .fan0r) hp (G.zorg x0 pl) rfl,
            qstepR_node_iterate hp _ (show (4 : ℕ) = 2 + 2 from rfl)]
        have ha1 : G.arity (G.face^[4] (G.edge (G.zorg x0 pl))) = QArity.qa7.toNat := by
          rw [G.arity_iterate_face]; exact hk
        have ha2 : G.arity (G.node (G.face^[4] (G.edge (G.zorg x0 pl))))
            = (topqa f1).toNat := by
          rw [node_iterate_face hp _ (show (4 : ℕ) = 3 + 1 from rfl)]
          have hfr : G.zmove .fan1r (G.zorg x0 pl1)
              = G.edge (G.face^[3] (G.edge (G.zorg x0 pl))) := by
            rw [hx1]; exact zmove_fanr_face hp _ rfl
          rw [← hfr]
          exact redPoplFan1R_fit hs hrec hval1 (by rw [hf1]; exact hq2) hredB
        have ha3 : G.arity (G.node (G.node (G.face^[4] (G.edge (G.zorg x0 pl)))))
            = (topqa f2).toNat := by
          rw [arity_node_node_iterate hp hc _ (show (4 : ℕ) = 3 + 1 from rfl)]
          have hfr : G.zmove .fan2r (G.zorg x0 pl1)
              = G.edge (G.face^[4] (G.edge (G.zorg x0 pl))) := by
            rw [hx1]; exact zmove_fanr_face hp _ rfl
          rw [← hfr]
          exact redPoplFan2R_fit hs hrec hval1 (by rw [hf2]; exact hq3) hredA
        have ht : qztGetr f2 (qztGetr f1 sqt)
            = QuizTree.get3 QArity.qa7 (topqa f1) (topqa f2) qt := by
          rw [← hg3, ← hg2, hsqt]
          rfl
        exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
      · split
        · rename_i hleaf
          rw [← Bool.not_eq_true]
          intro hcon
          rw [Bool.and_eq_true] at hcon
          obtain ⟨hredA, hredB⟩ := hcon
          have hv1 : (⟨.hatr, pl1, pr1⟩ : Zpart).Valid p0r := hval1
          have hv2 : (⟨.fan1r, pl1, pr1⟩ : Zpart).Valid p0r := hval1
          have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
          obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
          obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
          obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
          have hd1 : G.Zpfit x0 (G.qstepR (G.face^[5] (G.edge (G.zorg x0 pl))))
              ⟨.hatr, pl1, pr1⟩ := by
            intro _
            change G.zmove .hatr (G.zorg x0 pl1) = _
            rw [hx1, zmove_hatr_face hp hc (G.zorg x0 pl)
                (show G.arity (G.edge (G.zorg x0 pl)) = 1 + 6 from hk),
              qstepR_iterate hp hc _ (show (6 : ℕ) = 5 + 1 from rfl)]
          have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[5] (G.edge (G.zorg x0 pl)))))
              ⟨.fan1r, pl1, pr1⟩ := by
            intro _
            change G.zmove .fan1r (G.zorg x0 pl1) = _
            rw [hx1, zmove_fanr_face (zi := .fan1r) hp (G.zorg x0 pl) rfl,
              qstepR_node_iterate hp _ (show (5 : ℕ) = 3 + 2 from rfl)]
          have ha1 : G.arity (G.face^[5] (G.edge (G.zorg x0 pl))) = QArity.qa7.toNat := by
            rw [G.arity_iterate_face]; exact hk
          have ha2 : G.arity (G.node (G.face^[5] (G.edge (G.zorg x0 pl))))
              = (topqa f2).toNat := by
            rw [node_iterate_face hp _ (show (5 : ℕ) = 4 + 1 from rfl)]
            have hfr : G.zmove .fan2r (G.zorg x0 pl1)
                = G.edge (G.face^[4] (G.edge (G.zorg x0 pl))) := by
              rw [hx1]; exact zmove_fanr_face hp _ rfl
            rw [← hfr]
            exact redPoplFan2R_fit hs hrec hval1 (by rw [hf2]; exact hq2) hredB
          have ha3 : G.arity (G.node (G.node (G.face^[5] (G.edge (G.zorg x0 pl)))))
              = (topqa pr1.hat).toNat := by
            rw [arity_node_node_iterate hp hc _ (show (5 : ℕ) = 4 + 1 from rfl)]
            have hprev : G.arity (G.edge (G.face^[2] (G.edge (G.face (G.zorg x0 pl)))))
                = G.arity (G.edge (G.face^[5] (G.edge (G.zorg x0 pl)))) :=
              G.arity_hat_prev hp hc (G.zorg x0 pl)
                (show G.arity (G.edge (G.zorg x0 pl)) = 7 from hk) (by omega)
            rw [← hprev, ← hx1]
            exact redPoprHat_fit hs hrec hval1 hq3 hredA
          have ht : qztGetr pr1.hat (qztGetr f2 sqt)
              = QuizTree.get3 QArity.qa7 (topqa f2) (topqa pr1.hat) qt := by
            rw [← hg3, ← hg2, hsqt]
            rfl
          exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
        · rfl
  | cons8 hh f1 f2 f3 p =>
    have hk := redPoprSpoke_fit hs hrec hval hqs rfl
    have hf1 : pl1.fan1R = f1 := by rw [hpl1]; rfl
    have hf2 : pl1.fan2R = f2 := by rw [hpl1]; rfl
    have hf3 : pl1.fan3R = f3 := by rw [hpl1]; rfl
    rw [redZpartFan]
    split
    · rename_i hleaf
      rw [← Bool.not_eq_true]
      intro hcon
      rw [Bool.and_eq_true] at hcon
      obtain ⟨hredA, hredB⟩ := hcon
      have hv1 : (⟨.fan2l, pl1, pr1⟩ : Zpart).Valid p0r := hval1
      have hv2 : (⟨.hatl, pl, (Part.cons8 hh f1 f2 f3 p)⟩ : Zpart).Valid p0r := hval
      have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
      obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
      obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
      obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
      have hd1 : G.Zpfit x0 (G.qstepR (G.face^[3] (G.edge (G.zorg x0 pl))))
          ⟨.fan2l, pl1, pr1⟩ := by
        intro _
        change G.zmove .fan2l (G.zorg x0 pl1) = _
        rw [hx1, zmove_fanl_face (zi := .fan2l) hp (G.zorg x0 pl)
            (show G.arity (G.edge (G.zorg x0 pl)) = 4 + 4 from hk) rfl,
          qstepR_iterate hp hc _ (show (4 : ℕ) = 3 + 1 from rfl)]
      have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
          ⟨.hatl, pl, (Part.cons8 hh f1 f2 f3 p)⟩ := by
        intro _
        change G.zmove .hatl (G.zorg x0 pl) = _
        rw [zmove_hatl_eq hc, qstepR_node_iterate hp _ (show (3 : ℕ) = 1 + 2 from rfl)]
      have ha1 : G.arity (G.face^[3] (G.edge (G.zorg x0 pl))) = QArity.qa8.toNat := by
        rw [G.arity_iterate_face]; exact hk
      have ha2 : G.arity (G.node (G.face^[3] (G.edge (G.zorg x0 pl))))
          = (topqa hh).toNat := by
        rw [node_iterate_face hp _ (show (3 : ℕ) = 2 + 1 from rfl)]
        exact redPoprHat_fit hs hrec hval hq2 hredB
      have ha3 : G.arity (G.node (G.node (G.face^[3] (G.edge (G.zorg x0 pl)))))
          = (topqa f1).toNat := by
        rw [arity_node_node_iterate hp hc _ (show (3 : ℕ) = 2 + 1 from rfl)]
        have hfr : G.zmove .fan1r (G.zorg x0 pl1)
            = G.edge (G.face^[3] (G.edge (G.zorg x0 pl))) := by
          rw [hx1]; exact zmove_fanr_face hp _ rfl
        rw [← hfr]
        exact redPoplFan1R_fit hs hrec hval1 (by rw [hf1]; exact hq3) hredA
      have ht : qztGetr f1 (qztGetr hh sqt)
          = QuizTree.get3 QArity.qa8 (topqa hh) (topqa f1) qt := by
        rw [← hg3, ← hg2, hsqt]
        rfl
      exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
    · split
      · rename_i hleaf
        rw [← Bool.not_eq_true]
        intro hcon
        rw [Bool.and_eq_true] at hcon
        obtain ⟨hredA, hredB⟩ := hcon
        have hv1 : (⟨.fan1l, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        have hv2 : (⟨.fan0r, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
        obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
        obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
        obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
        have hd1 : G.Zpfit x0 (G.qstepR (G.face^[4] (G.edge (G.zorg x0 pl))))
            ⟨.fan1l, pl1, pr1⟩ := by
          intro _
          change G.zmove .fan1l (G.zorg x0 pl1) = _
          rw [hx1, zmove_fanl_face (zi := .fan1l) hp (G.zorg x0 pl)
              (show G.arity (G.edge (G.zorg x0 pl)) = 3 + 5 from hk) rfl,
            qstepR_iterate hp hc _ (show (5 : ℕ) = 4 + 1 from rfl)]
        have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[4] (G.edge (G.zorg x0 pl)))))
            ⟨.fan0r, pl1, pr1⟩ := by
          intro _
          change G.zmove .fan0r (G.zorg x0 pl1) = _
          rw [hx1, zmove_fanr_face (zi := .fan0r) hp (G.zorg x0 pl) rfl,
            qstepR_node_iterate hp _ (show (4 : ℕ) = 2 + 2 from rfl)]
        have ha1 : G.arity (G.face^[4] (G.edge (G.zorg x0 pl))) = QArity.qa8.toNat := by
          rw [G.arity_iterate_face]; exact hk
        have ha2 : G.arity (G.node (G.face^[4] (G.edge (G.zorg x0 pl))))
            = (topqa f1).toNat := by
          rw [node_iterate_face hp _ (show (4 : ℕ) = 3 + 1 from rfl)]
          have hfr : G.zmove .fan1r (G.zorg x0 pl1)
              = G.edge (G.face^[3] (G.edge (G.zorg x0 pl))) := by
            rw [hx1]; exact zmove_fanr_face hp _ rfl
          rw [← hfr]
          exact redPoplFan1R_fit hs hrec hval1 (by rw [hf1]; exact hq2) hredB
        have ha3 : G.arity (G.node (G.node (G.face^[4] (G.edge (G.zorg x0 pl)))))
            = (topqa f2).toNat := by
          rw [arity_node_node_iterate hp hc _ (show (4 : ℕ) = 3 + 1 from rfl)]
          have hfr : G.zmove .fan2r (G.zorg x0 pl1)
              = G.edge (G.face^[4] (G.edge (G.zorg x0 pl))) := by
            rw [hx1]; exact zmove_fanr_face hp _ rfl
          rw [← hfr]
          exact redPoplFan2R_fit hs hrec hval1 (by rw [hf2]; exact hq3) hredA
        have ht : qztGetr f2 (qztGetr f1 sqt)
            = QuizTree.get3 QArity.qa8 (topqa f1) (topqa f2) qt := by
          rw [← hg3, ← hg2, hsqt]
          rfl
        exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
      · split
        · rename_i hleaf
          rw [← Bool.not_eq_true]
          intro hcon
          rw [Bool.and_eq_true] at hcon
          obtain ⟨hredA, hredB⟩ := hcon
          have hv1 : (⟨.fan0l, pl1, pr1⟩ : Zpart).Valid p0r := hval1
          have hv2 : (⟨.fan1r, pl1, pr1⟩ : Zpart).Valid p0r := hval1
          have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
          obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
          obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
          obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
          have hd1 : G.Zpfit x0 (G.qstepR (G.face^[5] (G.edge (G.zorg x0 pl))))
              ⟨.fan0l, pl1, pr1⟩ := by
            intro _
            change G.zmove .fan0l (G.zorg x0 pl1) = _
            rw [hx1, zmove_fanl_face (zi := .fan0l) hp (G.zorg x0 pl)
                (show G.arity (G.edge (G.zorg x0 pl)) = 2 + 6 from hk) rfl,
              qstepR_iterate hp hc _ (show (6 : ℕ) = 5 + 1 from rfl)]
          have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[5] (G.edge (G.zorg x0 pl)))))
              ⟨.fan1r, pl1, pr1⟩ := by
            intro _
            change G.zmove .fan1r (G.zorg x0 pl1) = _
            rw [hx1, zmove_fanr_face (zi := .fan1r) hp (G.zorg x0 pl) rfl,
              qstepR_node_iterate hp _ (show (5 : ℕ) = 3 + 2 from rfl)]
          have ha1 : G.arity (G.face^[5] (G.edge (G.zorg x0 pl))) = QArity.qa8.toNat := by
            rw [G.arity_iterate_face]; exact hk
          have ha2 : G.arity (G.node (G.face^[5] (G.edge (G.zorg x0 pl))))
              = (topqa f2).toNat := by
            rw [node_iterate_face hp _ (show (5 : ℕ) = 4 + 1 from rfl)]
            have hfr : G.zmove .fan2r (G.zorg x0 pl1)
                = G.edge (G.face^[4] (G.edge (G.zorg x0 pl))) := by
              rw [hx1]; exact zmove_fanr_face hp _ rfl
            rw [← hfr]
            exact redPoplFan2R_fit hs hrec hval1 (by rw [hf2]; exact hq2) hredB
          have ha3 : G.arity (G.node (G.node (G.face^[5] (G.edge (G.zorg x0 pl)))))
              = (topqa f3).toNat := by
            rw [arity_node_node_iterate hp hc _ (show (5 : ℕ) = 4 + 1 from rfl)]
            have hfr : G.zmove .fan3r (G.zorg x0 pl1)
                = G.edge (G.face^[5] (G.edge (G.zorg x0 pl))) := by
              rw [hx1]; exact zmove_fanr_face hp _ rfl
            rw [← hfr]
            exact redPoplFan3R_fit hs hrec hval1 (by rw [hf3]; exact hq3) hredA
          have ht : qztGetr f3 (qztGetr f2 sqt)
              = QuizTree.get3 QArity.qa8 (topqa f2) (topqa f3) qt := by
            rw [← hg3, ← hg2, hsqt]
            rfl
          exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht hleaf
        · split
          · rename_i hleaf
            rw [← Bool.not_eq_true]
            intro hcon
            rw [Bool.and_eq_true] at hcon
            obtain ⟨hredA, hredB⟩ := hcon
            have hv1 : (⟨.hatr, pl1, pr1⟩ : Zpart).Valid p0r := hval1
            have hv2 : (⟨.fan2r, pl1, pr1⟩ : Zpart).Valid p0r := hval1
            have hv3 : (⟨.nil, pl1, pr1⟩ : Zpart).Valid p0r := hval1
            obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
            obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
            obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
            have hd1 : G.Zpfit x0 (G.qstepR (G.face^[6] (G.edge (G.zorg x0 pl))))
                ⟨.hatr, pl1, pr1⟩ := by
              intro _
              change G.zmove .hatr (G.zorg x0 pl1) = _
              rw [hx1, zmove_hatr_face hp hc (G.zorg x0 pl)
                  (show G.arity (G.edge (G.zorg x0 pl)) = 1 + 7 from hk),
                qstepR_iterate hp hc _ (show (7 : ℕ) = 6 + 1 from rfl)]
            have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[6] (G.edge (G.zorg x0 pl)))))
                ⟨.fan2r, pl1, pr1⟩ := by
              intro _
              change G.zmove .fan2r (G.zorg x0 pl1) = _
              rw [hx1, zmove_fanr_face (zi := .fan2r) hp (G.zorg x0 pl) rfl,
                qstepR_node_iterate hp _ (show (6 : ℕ) = 4 + 2 from rfl)]
            have ha1 : G.arity (G.face^[6] (G.edge (G.zorg x0 pl))) = QArity.qa8.toNat := by
              rw [G.arity_iterate_face]; exact hk
            have ha2 : G.arity (G.node (G.face^[6] (G.edge (G.zorg x0 pl))))
                = (topqa f3).toNat := by
              rw [node_iterate_face hp _ (show (6 : ℕ) = 5 + 1 from rfl)]
              have hfr : G.zmove .fan3r (G.zorg x0 pl1)
                  = G.edge (G.face^[5] (G.edge (G.zorg x0 pl))) := by
                rw [hx1]; exact zmove_fanr_face hp _ rfl
              rw [← hfr]
              exact redPoplFan3R_fit hs hrec hval1 (by rw [hf3]; exact hq2) hredB
            have ha3 : G.arity (G.node (G.node (G.face^[6] (G.edge (G.zorg x0 pl)))))
                = (topqa pr1.hat).toNat := by
              rw [arity_node_node_iterate hp hc _ (show (6 : ℕ) = 5 + 1 from rfl)]
              have hprev : G.arity (G.edge (G.face^[2] (G.edge (G.face (G.zorg x0 pl)))))
                  = G.arity (G.edge (G.face^[6] (G.edge (G.zorg x0 pl)))) :=
                G.arity_hat_prev hp hc (G.zorg x0 pl)
                  (show G.arity (G.edge (G.zorg x0 pl)) = 8 from hk) (by omega)
              rw [← hprev, ← hx1]
              exact redPoprHat_fit hs hrec hval1 hq3 hredA
            have ht : qztGetr pr1.hat (qztGetr f3 sqt)
                = QuizTree.get3 QArity.qa8 (topqa f3) (topqa pr1.hat) qt := by
              rw [← hg3, ← hg2, hsqt]
              rfl
            exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 (zpfit_nil _ _ _) ha1 ha2 ha3 ht
              hleaf
          · rfl

omit [Finite D] in
/-- Shifting a zipper whose right sector has at least two subparts. -/
theorem zshiftr_eq (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) (h0 : zp.right ≠ .nil)
    (h1 : zp.right.size ≠ 1) :
    zshiftr p0l p0r zi zp = ⟨zi, Part.shift zp.right zp.left, zp.right.drop 1⟩ := by
  unfold zshiftr
  rw [ite_eq_right h0, ite_eq_right h1]

/-- No test at one subpart can succeed, under the standing assumptions. -/
theorem not_redZpartStep (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {qt : QuizTree} (hqt : ∀ y : D, ¬ G.Fit y qt) {pl pr : Part} (hpr2 : 2 ≤ pr.size)
    (hval : Zvalid p0r pl pr) : redZpartStep redRec ahub p0l p0r qt pl pr = false := by
  have hp := hs.plain
  have hc := hs.cubic
  have hpr : pr ≠ .nil := by
    intro h; rw [h] at hpr2; simp only [Part.size] at hpr2; omega
  have hval1 : Zvalid p0r (Part.shift pr pl) (pr.drop 1) := hval.shiftRight
  have hx1 : G.zorg x0 (Part.shift pr pl) = G.face (G.zorg x0 pl) := zorg_shift x0 hpr pl
  rw [redZpartStep]
  split
  · rename_i hsqt
    obtain ⟨hqs, hgs, -⟩ := qztGetr_fit hsqt
    have hsq : qztGetr pr.spoke (QuizTree.truncate qt) = QuizTree.get1 (topqa pr.spoke) qt := by
      rw [← hgs]
      exact QuizTree.get1_truncate (topqa pr.spoke) qt (by rw [hgs]; exact hsqt)
    split
    · rename_i hleaf
      rw [← Bool.not_eq_true]
      intro hcon
      rw [Bool.and_eq_true] at hcon
      obtain ⟨hredA, hredB⟩ := hcon
      have hv1 : (⟨.hubr, Part.shift pr pl, pr.drop 1⟩ : Zpart).Valid p0r := hval1
      have hv2 : (zshiftl p0l p0r .hubl ⟨.hub, pl, pr⟩).Valid p0r := valid_zshiftl hs _ hval
      have hv3 : (⟨.hat, pl, pr⟩ : Zpart).Valid p0r := hval
      obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
      obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
      obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
      have hd1 : G.Zpfit x0 (G.qstepR (G.zorg x0 pl)) ⟨.hubr, Part.shift pr pl, pr.drop 1⟩ := by
        intro _
        change G.node (G.node (G.zorg x0 (Part.shift pr pl))) = _
        rw [hx1, hp.node_face]
        rfl
      have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.zorg x0 pl)))
          (zshiftl p0l p0r .hubl ⟨.hub, pl, pr⟩) := by
        intro _
        rw [zdart_zshiftl hs]
        rfl
      have hd3 : G.Zpfit x0 (G.qstepR (G.node (G.node (G.zorg x0 pl)))) ⟨.hat, pl, pr⟩ := by
        intro _
        rfl
      have ha1 : G.arity (G.zorg x0 pl) = ahub.toNat := arity_zorg hs pl
      have ha2 : G.arity (G.node (G.zorg x0 pl)) = (topqa pl.spoke).toNat :=
        redPoplSpoke_fit hs hrec hval hq2 hredB
      have ha3 : G.arity (G.node (G.node (G.zorg x0 pl))) = (topqa pr.spoke).toNat := by
        rw [hc.node_node, G.arity_face]
        exact redPoprSpoke_fit hs hrec hval hq3 hredA
      have ht : qztGetr pr.spoke (qztGetr pl.spoke (QuizTree.get1 ahub qt))
          = QuizTree.get3 ahub (topqa pl.spoke) (topqa pr.spoke) qt := by
        rw [← hg3, ← hg2]
        rfl
      exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 hd3 ha1 ha2 ha3 ht hleaf
    · split
      · rename_i hleaf
        rw [← Bool.not_eq_true]
        intro hcon
        rw [Bool.and_eq_true, Bool.and_eq_true] at hcon
        obtain ⟨⟨hredA, hredB⟩, hredC⟩ := hcon
        have hk : G.arity (G.edge (G.zorg x0 pl)) = (topqa pr.spoke).toNat :=
          redPoprSpoke_fit hs hrec hval hqs hredC
        have hv1 : (⟨zfanLt pr, Part.shift pr pl, pr.drop 1⟩ : Zpart).Valid p0r := hval1
        have hv2 : (⟨.hub, pl, pr⟩ : Zpart).Valid p0r := hval
        have hv3 : (⟨zfanRt pl, pl, pr⟩ : Zpart).Valid p0r := hval
        obtain ⟨hprop, -⟩ := redQztLeaf_fit hs hrec hv1 hv2 hv3 _ hleaf
        obtain ⟨hq3, hg3, hprop2⟩ := qztGetr_fit hprop
        obtain ⟨hq2, hg2, -⟩ := qztGetr_fit hprop2
        have hzd : G.zdart x0 ⟨.hatr, pl, pr⟩ = G.face^[2] (G.edge (G.zorg x0 pl)) := by
          change G.face (G.node (G.node (G.zorg x0 pl))) = _
          rw [hc.node_node, face_two]
        have htopr : G.ZpfitTop ahub x0 ⟨.hatr, pl, pr⟩ := by
          change G.arity (G.zmove .hatr (G.zorg x0 pl)) = _
          rw [arity_zmove_hatr hc]
          exact hk
        have htopl : G.ZpfitTop ahub x0 ⟨.hatl, pl, pr⟩ := by
          change G.arity (G.zmove .hatl (G.zorg x0 pl)) = _
          rw [arity_zmove_hatl]
          exact redPoplSpoke_fit hs hrec hval hq2 hredB
        have hd1 : G.Zpfit x0 (G.qstepR (G.face^[2] (G.edge (G.zorg x0 pl))))
            ⟨zfanLt pr, Part.shift pr pl, pr.drop 1⟩ := by
          have hzs : zstepRt p0l p0r ⟨.hatr, pl, pr⟩
              = ⟨zfanLt pr, Part.shift pr pl, pr.drop 1⟩ :=
            zshiftr_eq p0l p0r (zfanLt pr) ⟨.hatr, pl, pr⟩ hpr (by change pr.size ≠ 1; omega)
          have h := zdart_stepRt hs htopr hval (zp := ⟨.hatr, pl, pr⟩)
          rw [hzs, hzd] at h
          exact h
        have hd2 : G.Zpfit x0 (G.qstepR (G.node (G.face^[2] (G.edge (G.zorg x0 pl)))))
            ⟨.hub, pl, pr⟩ := by
          intro _
          change G.zorg x0 pl = _
          rw [qstepR_node_iterate hp _ (show (2 : ℕ) = 0 + 2 from rfl)]
          change _ = G.edge (G.edge (G.zorg x0 pl))
          rw [hp.edge_edge]
        have hd3 : G.Zpfit x0 (G.qstepR (G.node (G.node (G.face^[2] (G.edge (G.zorg x0 pl))))))
            ⟨zfanRt pl, pl, pr⟩ := by
          intro hprp
          have h := zdart_stepLt hs htopl hval (zp := ⟨.hatl, pl, pr⟩)
          refine (h hprp).trans ?_
          zsimp hp, hc
        have ha1 : G.arity (G.face^[2] (G.edge (G.zorg x0 pl))) = (topqa pr.spoke).toNat := by
          rw [G.arity_iterate_face]; exact hk
        have ha2 : G.arity (G.node (G.face^[2] (G.edge (G.zorg x0 pl))))
            = (topqa pl.spoke).toNat := by
          have hfe : G.face (G.edge (G.face (G.edge (G.zorg x0 pl)))) = G.node (G.zorg x0 pl) := by
            rw [face_edge_face G hp hc, hp.edge_edge]
          rw [node_iterate_face hp _ (show (2 : ℕ) = 1 + 1 from rfl), Function.iterate_one,
            ← G.arity_face (G.edge (G.face (G.edge (G.zorg x0 pl)))), hfe]
          exact redPoplSpoke_fit hs hrec hval hq2 hredB
        have ha3 : G.arity (G.node (G.node (G.face^[2] (G.edge (G.zorg x0 pl)))))
            = (topqa pr.hat).toNat := by
          rw [arity_node_node_iterate hp hc _ (show (2 : ℕ) = 1 + 1 from rfl)]
          exact redPoprHat_fit hs hrec hval hq3 hredA
        have ht : qztGetr pr.hat (qztGetr pl.spoke (qztGetr pr.spoke (QuizTree.truncate qt)))
            = QuizTree.get3 (topqa pr.spoke) (topqa pl.spoke) (topqa pr.hat) qt := by
          rw [← hg3, ← hg2, hsq]
          rfl
        exact leaf_absurd hs hrec hqt _ hv1 hv2 hv3 hd1 hd2 hd3 ha1 ha2 ha3 ht hleaf
      · exact not_redZpartFan hs hrec hqt rfl hpr hval hval1 hx1 hqs hsq
  · rfl

/-- The reducibility walk fails at every depth. -/
theorem not_redZpartRec (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {qt : QuizTree} (hqt : ∀ y : D, ¬ G.Fit y qt) :
    ∀ (d : ℕ) (pl pr : Part), d < pr.size → Zvalid p0r pl pr →
      redZpartRec redRec ahub p0l p0r qt pl pr d = false := by
  intro d
  induction d with
  | zero => intro pl pr _ _; rfl
  | succ d ih =>
    intro pl pr hd hval
    rw [redZpartRec, not_redZpartStep hs hrec hqt (by omega) hval,
      ih _ _ (by rw [Part.size_drop]; omega) hval.shiftRight]
    rfl

/-- The reducibility walk around the whole hub fails. -/
theorem not_redZpart (hs : G.Setup ahub p0l p0r x0) (hrec : G.NotRedRec redRec ahub)
    {qt : QuizTree} (hqt : ∀ y : D, ¬ G.Fit y qt) :
    redZpart redRec ahub p0l p0r qt = false := by
  have hp0l : p0l ≠ .nil := by
    intro h
    have h1 := hs.size_p0l
    rw [h] at h1
    have h2 := five_le_toNat ahub
    simp only [Part.size] at h1
    omega
  refine not_redZpartRec hs hrec hqt _ _ _ ?_ hs.zvalid_init.shiftLeft
  rw [Part.size_shift_of_ne_nil hp0l, hs.size_p0r]
  omega

end Hypermap

/-! ### The reducibility check -/

/-- The recursive reducibility check, with a fuel bound on the recursion. -/
def redpartLoop (qt : QuizTree) (ahub : QArity) : ℕ → Part → Bool
  | 0, _ => false
  | d + 1, p => redZpart (redpartLoop qt ahub d) ahub p.rev p qt

/-- `redpart qt p` holds when every 2-neighbourhood matching the part `p`
contains an embedded configuration kernel from the quiz tree `qt`.  The bound
`p.size * 12` on the recursion depth is generous: each recursive call pops one
range, there are at most four open ranges per sector, and the worst case would
need a configuration all but one of whose faces is an octagon. -/
def redpart (qt : QuizTree) (p : Part) : Bool :=
  decide (p.size = (QArity.ofArity p.size).toNat) &&
    redpartLoop qt (QArity.ofArity p.size) (p.size * 12) p

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D}

/-- The recursive check rejects every part that some dart of the right hub
arity fits exactly. -/
theorem not_redpartLoop (hG : G.PlainCubicPentagonal) {qt : QuizTree}
    (hqt : ∀ y : D, ¬ G.Fit y qt) (ahub : QArity) :
    ∀ (d : ℕ) (p : Part) (x : D), G.ExactFitp x p → p.size = ahub.toNat →
      redpartLoop qt ahub d p = false := by
  intro d
  induction d with
  | zero => intro p x _ _; rfl
  | succ d ih =>
    intro p x hfit hsz
    have hax : G.arity x = ahub.toNat := hfit.1.trans hsz
    have hs : G.Setup ahub p.rev p x := ⟨hG, rfl, hfit, hax⟩
    have hrec : G.NotRedRec (redpartLoop qt ahub d) ahub := by
      intro y q hay hq
      exact ih q y hq (hq.1.symm.trans hay)
    exact not_redZpart hs hrec hqt

/-- Soundness of the reducibility check: a part accepted by `redpart` fits no
dart of a plain cubic pentagonal map whose quiz tree fits nowhere. -/
theorem no_fit_redpart (hG : G.PlainCubicPentagonal) {qt : QuizTree}
    (hqt : ∀ y : D, ¬ G.Fit y qt) {p : Part} (h : redpart qt p = true) (x : D) :
    ¬ G.ExactFitp x p := by
  intro hfit
  rw [redpart, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hsz, hloop⟩ := h
  rw [not_redpartLoop hG hqt _ _ p x hfit hsz] at hloop
  exact Bool.noConfusion hloop

end Hypermap

end FourColor

import FourColor.Geometry
import FourColor.Coloring

/-!
# Quizzes: question trees that locate a configuration

A *question* is a small tree of arity tests: at a dart of a cubic hypermap it
checks the arity of the face, then moves to a neighbouring node — left, right,
or both — and asks again.  A *quiz* is a pair of questions, asked at the two
ends of an edge.  Walking a question at a dart lists the darts it visits; the
question *fits* there when the arities of those darts are the ones the question
records.  This is the test used later to recognise an embedded configuration.

## Main definitions

* `QArity` — the face arities a configuration can have, 5 to 11.
* `Question`, `Quiz` — question trees and pairs of them, with their mirror
  images (`Question.flip`, `Quiz.flip`) and recorded arities (`Question.flat`).
* `Hypermap.qstepL`, `Hypermap.qstepR` — the left and right moves at a node.
* `Hypermap.walkq`, `Hypermap.fitq`, `Hypermap.walkqz`, `Hypermap.fitqz`.
* `Hypermap.embedqz` — the partial map from the configuration map to the
  searched map that a quiz fitting both determines.

## Main results

* `Hypermap.quiz_preembedding` — a quiz valid for a configuration ring that
  also fits a plain cubic map gives a `Preembedding` of the configuration
  kernel into that map.
-/

namespace FourColor

/-- The face arities that occur in a configuration: 5 to 11. -/
inductive QArity
  | qa5 | qa6 | qa7 | qa8 | qa9 | qa10 | qa11
  deriving DecidableEq, Repr

namespace QArity

/-- The arity a `QArity` stands for. -/
def toNat : QArity → ℕ
  | qa5 => 5
  | qa6 => 6
  | qa7 => 7
  | qa8 => 8
  | qa9 => 9
  | qa10 => 10
  | qa11 => 11

instance : Coe QArity ℕ := ⟨toNat⟩

/-- The `QArity` with a given value, defaulting to `qa11`. -/
def ofArity : ℕ → QArity
  | 5 => qa5
  | 6 => qa6
  | 7 => qa7
  | 8 => qa8
  | 9 => qa9
  | 10 => qa10
  | _ => qa11

@[simp] theorem ofArity_toNat (qa : QArity) : ofArity qa.toNat = qa := by
  cases qa <;> rfl

end QArity

/-- An embedding test tree: check the arity here, then move and ask again.
`askL`/`askR` move once, `askLL`/`askRR` move twice (for configurations whose
interior has an articulation), and `askLR` branches both ways. -/
inductive Question
  | ask0
  | ask1 (qa : QArity)
  | askL (qa : QArity) (ql : Question)
  | askR (qa : QArity) (qr : Question)
  | askLR (qa : QArity) (ql qr : Question)
  | askLL (qa : QArity) (qll : Question)
  | askRR (qa : QArity) (qrr : Question)
  deriving DecidableEq, Repr

namespace Question

/-- Whether the question starts with a right move. -/
def IsAskR : Question → Prop
  | askR _ _ => True
  | _ => False

instance (q : Question) : Decidable q.IsAskR := by
  cases q <;> simp only [IsAskR] <;> infer_instance

/-- The arities the question records, in prefix order. -/
def flat : Question → List ℕ
  | ask0 => []
  | ask1 qa => [qa.toNat]
  | askL qa ql => qa.toNat :: ql.flat
  | askR qa qr => qa.toNat :: qr.flat
  | askLR qa ql qr => qa.toNat :: (ql.flat ++ qr.flat)
  | askLL qa qll => qa.toNat :: qll.flat
  | askRR qa qrr => qa.toNat :: qrr.flat

/-- The mirror image of a question, with left and right exchanged. -/
def flip : Question → Question
  | askL qa ql => askR qa ql.flip
  | askR qa qr => askL qa qr.flip
  | askLR qa ql qr => askLR qa qr.flip ql.flip
  | askLL qa qll => askRR qa qll.flip
  | askRR qa qrr => askLL qa qrr.flip
  | q => q

@[simp] theorem flip_flip (q : Question) : q.flip.flip = q := by
  induction q with
  | ask0 => rfl
  | ask1 _ => rfl
  | askL _ _ ih => simp [flip, ih]
  | askR _ _ ih => simp [flip, ih]
  | askLR _ _ _ ihl ihr => simp [flip, ihl, ihr]
  | askLL _ _ ih => simp [flip, ih]
  | askRR _ _ ih => simp [flip, ih]

@[simp] theorem length_flat_flip (q : Question) : q.flip.flat.length = q.flat.length := by
  induction q with
  | ask0 => rfl
  | ask1 _ => rfl
  | askL _ _ ih => simpa [flip, flat] using ih
  | askR _ _ ih => simpa [flip, flat] using ih
  | askLR _ _ _ ihl ihr => simp [flip, flat, ihl, ihr, Nat.add_comm]
  | askLL _ _ ih => simpa [flip, flat] using ih
  | askRR _ _ ih => simpa [flip, flat] using ih

end Question

/-- An embedding test: two questions, asked at the two ends of an edge. -/
structure Quiz where
  /-- The question asked at the dart itself. -/
  fst : Question
  /-- The question asked at the other end of its edge. -/
  snd : Question
  deriving DecidableEq, Repr

namespace Quiz

/-- Both questions start with a right move. -/
def IsQuizR (qz : Quiz) : Prop := qz.fst.IsAskR ∧ qz.snd.IsAskR

instance (qz : Quiz) : Decidable qz.IsQuizR := by
  unfold IsQuizR; infer_instance

/-- The arities both questions record. -/
def flat (qz : Quiz) : List ℕ := qz.fst.flat ++ qz.snd.flat

/-- The mirror image of a quiz: the two questions are mirrored and swapped,
keeping the initial right moves in place. -/
def flip (qz : Quiz) : Quiz :=
  match qz with
  | ⟨.askR qa₀ q₀₁, .askR qa₁ q₁₀⟩ => ⟨.askR qa₀ q₁₀.flip, .askR qa₁ q₀₁.flip⟩
  | qz => qz

end Quiz

namespace Hypermap

variable {D : Type*} (G : Hypermap D)

/-- The left move at a node of a cubic hypermap. -/
def qstepL (x : D) : D := G.node (G.edge (G.node x))

/-- The right move at a node of a cubic hypermap. -/
def qstepR (x : D) : D := G.node (G.edge x)

/-- The darts a question visits, in prefix order. -/
def walkq (x : D) : Question → List D
  | .ask0 => []
  | .ask1 _ => [x]
  | .askL _ ql => x :: walkq (G.qstepL x) ql
  | .askR _ qr => x :: walkq (G.qstepR x) qr
  | .askLR _ ql qr => x :: (walkq (G.qstepL x) ql ++ walkq (G.qstepR x) qr)
  | .askLL _ qll =>
      G.edge (G.node (G.qstepL x)) :: walkq (G.qstepL (G.qstepL x)) qll
  | .askRR _ qrr => G.qstepR x :: walkq (G.qstepR (G.qstepR x)) qrr

/-- A question fits at a dart when the arities it records are those of the
darts it visits. -/
def Fitq (x : D) (q : Question) : Prop := q.flat = (G.walkq x q).map G.arity

@[simp] theorem length_walkq (x : D) (q : Question) :
    (G.walkq x q).length = q.flat.length := by
  induction q generalizing x with
  | ask0 => rfl
  | ask1 _ => rfl
  | askL _ _ ih => simp [walkq, Question.flat, ih]
  | askR _ _ ih => simp [walkq, Question.flat, ih]
  | askLR _ _ _ ihl ihr => simp [walkq, Question.flat, ihl, ihr]
  | askLL _ _ ih => simp [walkq, Question.flat, ih]
  | askRR _ _ ih => simp [walkq, Question.flat, ih]

/-- Fitting splits along a concatenation, because the walk has exactly as many
darts as the question has arities. -/
theorem fitq_append (x : D) (q : Question) (sa : List ℕ) (s : List D) :
    (q.flat ++ sa = (G.walkq x q ++ s).map G.arity) ↔
      (G.Fitq x q ∧ sa = s.map G.arity) := by
  have hlen := G.length_walkq x q
  rw [List.map_append]
  constructor
  · intro h
    have h1 : q.flat = (G.walkq x q).map G.arity := by
      have := congrArg (List.take q.flat.length) h
      rwa [List.take_left' (by simp), List.take_left' (by simp [hlen])] at this
    refine ⟨h1, ?_⟩
    have := congrArg (List.drop q.flat.length) h
    rwa [List.drop_left' (by simp), List.drop_left' (by simp [hlen])] at this
  · rintro ⟨h1, h2⟩
    rw [← h1, ← h2]

/-- The darts a quiz visits: those of the first question at the dart, then
those of the second at the other end of its edge. -/
def walkqz (x : D) (qz : Quiz) : List D :=
  G.walkq x qz.fst ++ G.walkq (G.edge x) qz.snd

/-- A quiz fits at a dart when both its questions do. -/
def Fitqz (x : D) (qz : Quiz) : Prop := qz.flat = (G.walkqz x qz).map G.arity

@[simp] theorem length_walkqz (x : D) (qz : Quiz) :
    (G.walkqz x qz).length = qz.flat.length := by
  simp [walkqz, Quiz.flat]

/-- `qz` tests for the configuration with perimeter `rc` at the dart `x₀`: it
is a right quiz, it fits at `x₀`, and the darts it visits are a transversal of
the faces of the kernel of `rc`. -/
def ValidQuiz (rc : List D) (x₀ : D) (qz : Quiz) : Prop :=
  qz.IsQuizR ∧ G.Fitqz x₀ qz ∧ G.Simple (G.walkqz x₀ qz) ∧
    ∀ y, G.Fband (G.walkqz x₀ qz) y ↔ G.Kernel rc y

/-! ### Mirror images

In a plain cubic hypermap the two moves are exchanged by mirroring, so a
question fits the mirror exactly when its mirror image fits the map.  The extra
`face` shift in the doubled moves does not affect the test, because arity is
constant on a face.
-/

theorem face_eq_node_inv_mul_edge_inv : G.face = G.node⁻¹ * G.edge⁻¹ := by
  have h := G.node_face_edge
  have h1 : G.node * G.face = G.edge⁻¹ := mul_eq_one_iff_eq_inv.mp h
  rw [← h1, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mirror_qstepR (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.mirror.qstepR x = G.qstepL x := by
  have he : G.edge⁻¹ = G.edge :=
    inv_eq_of_mul_eq_one_right (by have := hp.edge_pow_two; rwa [pow_two] at this)
  have hn : G.node⁻¹ = G.node * G.node :=
    inv_eq_of_mul_eq_one_right (by
      have := hc.node_pow_three
      rwa [pow_succ, pow_two] at this)
  change G.mirror.node (G.mirror.edge x) = G.node (G.edge (G.node x))
  rw [mirror_node, mirror_edge, Equiv.Perm.mul_apply, face_eq_node_inv_mul_edge_inv,
    Equiv.Perm.mul_apply, he, hn, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have h3 : G.node (G.node (G.node (G.edge (G.node x)))) = G.edge (G.node x) := by
    have := hc.node_node_node (G.edge (G.node x))
    exact this
  rw [h3]

theorem mirror_qstepL (hp : G.Plain) (hc : G.Cubic) (x : D) :
    G.mirror.qstepL x = G.qstepR x := by
  have he : G.edge⁻¹ = G.edge :=
    inv_eq_of_mul_eq_one_right (by have := hp.edge_pow_two; rwa [pow_two] at this)
  have hn : G.node⁻¹ = G.node * G.node :=
    inv_eq_of_mul_eq_one_right (by
      have := hc.node_pow_three
      rwa [pow_succ, pow_two] at this)
  change G.mirror.node (G.mirror.edge (G.mirror.node x)) = G.node (G.edge x)
  rw [mirror_node, mirror_edge, face_eq_node_inv_mul_edge_inv]
  simp only [Equiv.Perm.mul_apply, he, hn]
  have h1 : G.node (G.node (G.node x)) = x := hc.node_node_node x
  rw [h1]
  have h2 : G.node (G.node (G.node (G.edge x))) = G.edge x :=
    hc.node_node_node (G.edge x)
  rw [h2]

private theorem append_eq_append_iff_of_length {α : Type*} {a b c d : List α}
    (h : a.length = c.length) : (a ++ b = c ++ d) ↔ (a = c ∧ b = d) := by
  constructor
  · intro heq
    exact List.append_inj heq h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mirror_edge_mirror_node (u : D) : G.mirror.edge (G.mirror.node u) = G.face u := by
  change (G.face * G.node) (G.node⁻¹ u) = G.face u
  rw [Equiv.Perm.mul_apply]
  simp

theorem arity_edge_node [Finite D] (u : D) : G.arity (G.edge (G.node u)) = G.arity u := by
  conv_rhs => rw [← G.nodeK u]
  rw [arity_face]

/-- In a plain cubic hypermap a question fits the mirror exactly when its
mirror image fits the map. -/
theorem fitq_mirror_flip [Finite D] (hp : G.Plain) (hc : G.Cubic) : ∀ (q : Question) (x : D),
    G.mirror.Fitq x q.flip ↔ G.Fitq x q := by
  intro q
  induction q with
  | ask0 => intro x; simp [Fitq, Question.flip, Question.flat, walkq]
  | ask1 qa => intro x; simp [Fitq, Question.flip, Question.flat, walkq]
  | askL qa ql ih =>
    intro x
    simp only [Question.flip, Fitq, Question.flat, walkq, mirror_qstepR G hp hc,
      List.map_cons, arity_mirror, List.cons.injEq]
    exact and_congr_right fun _ => ih (G.qstepL x)
  | askR qa qr ih =>
    intro x
    simp only [Question.flip, Fitq, Question.flat, walkq, mirror_qstepL G hp hc,
      List.map_cons, arity_mirror, List.cons.injEq]
    exact and_congr_right fun _ => ih (G.qstepR x)
  | askLR qa ql qr ihl ihr =>
    intro x
    simp only [Question.flip, Fitq, Question.flat, walkq, mirror_qstepL G hp hc,
      mirror_qstepR G hp hc, List.map_cons, List.map_append, arity_mirror,
      List.cons.injEq]
    refine and_congr_right fun _ => ?_
    rw [append_eq_append_iff_of_length (by simp [Question.length_flat_flip]),
      append_eq_append_iff_of_length (by simp)]
    rw [and_comm]
    exact and_congr (ihl (G.qstepL x)) (ihr (G.qstepR x))
  | askLL qa qll ih =>
    intro x
    simp only [Question.flip, Fitq, Question.flat, walkq, mirror_qstepL G hp hc,
      mirror_qstepR G hp hc, List.map_cons, arity_mirror, List.cons.injEq]
    refine and_congr ?_ (ih (G.qstepL (G.qstepL x)))
    -- the doubled move differs by a face shift, which arity does not see
    rw [arity_edge_node]
  | askRR qa qrr ih =>
    intro x
    simp only [Question.flip, Fitq, Question.flat, walkq, mirror_qstepL G hp hc,
      mirror_qstepR G hp hc, List.map_cons, arity_mirror, List.cons.injEq]
    refine and_congr ?_ (ih (G.qstepR (G.qstepR x)))
    rw [mirror_edge_mirror_node, arity_face]

theorem fitq_flip_mirror [Finite D] (hp : G.Plain) (hc : G.Cubic) (q : Question) (x : D) :
    G.Fitq x q.flip ↔ G.mirror.Fitq x q := by
  have h := fitq_mirror_flip G hp hc q.flip x
  rw [Question.flip_flip] at h
  exact h.symm
  
/-- A right question is one that starts with a right move. -/
theorem Question.exists_of_isAskR {q : Question} (h : q.IsAskR) :
    ∃ qa q', q = .askR qa q' := by
  cases q <;> simp_all [Question.IsAskR]

theorem node_face (hp : G.Plain) (x : D) : G.node (G.face x) = G.edge x := by
  have hface : G.face = G.node⁻¹ * G.edge⁻¹ := face_eq_node_inv_mul_edge_inv G
  have he : G.edge⁻¹ = G.edge :=
    inv_eq_of_mul_eq_one_right (by have := hp.edge_pow_two; rwa [pow_two] at this)
  rw [hface, Equiv.Perm.mul_apply, he]
  simp

/-- Mirroring exchanges the two ends of the edge a quiz is asked across. -/
theorem mirror_edge_face (hp : G.Plain) (x : D) :
    G.mirror.edge (G.face x) = G.face (G.edge x) := by
  change (G.face * G.node) (G.face x) = G.face (G.edge x)
  rw [Equiv.Perm.mul_apply, node_face G hp]

/-- In a plain cubic hypermap a quiz fits the mirror at `face x` exactly when
its mirror image fits the map at `x`. -/
theorem fitqz_flip [Finite D] (hp : G.Plain) (hc : G.Cubic) {qz : Quiz}
    (hqz : qz.IsQuizR) (x : D) : G.Fitqz x qz.flip ↔ G.mirror.Fitqz (G.face x) qz := by
  obtain ⟨qa₀, q₀₁, h0⟩ := Question.exists_of_isAskR hqz.1
  obtain ⟨qa₁, q₁₀, h1⟩ := Question.exists_of_isAskR hqz.2
  obtain ⟨f, s⟩ := qz
  subst h0
  subst h1
  -- the darts the two sides visit
  have hee : ∀ y : D, G.edge (G.edge y) = y := hp.edge_edge
  have hmef : G.mirror.edge (G.face x) = G.face (G.edge x) := mirror_edge_face G hp x
  have hstepR : G.qstepR (G.edge x) = G.node x := by
    change G.node (G.edge (G.edge x)) = G.node x
    rw [hee]
  have hmstep₁ : G.mirror.qstepR (G.face x) = G.node x := by
    rw [mirror_qstepR G hp hc]
    change G.node (G.edge (G.node (G.face x))) = G.node x
    rw [node_face G hp, hee]
  have hmstep₂ : G.mirror.qstepR (G.face (G.edge x)) = G.qstepR x := by
    rw [mirror_qstepR G hp hc]
    change G.node (G.edge (G.node (G.face (G.edge x)))) = G.node (G.edge x)
    rw [node_face G hp, hee]
  -- split both sides into their four pieces
  simp only [Quiz.flip, Quiz.flat, Fitqz, walkqz, Question.flat, walkq, List.map_append,
    List.map_cons, List.cons_append, arity_mirror, hmef, hmstep₁, hmstep₂, hstepR,
    List.cons.injEq, arity_face]
  rw [append_eq_append_iff_of_length (by simp [Question.length_flat_flip]),
    append_eq_append_iff_of_length (by simp)]
  simp only [List.cons.injEq]
  rw [← Fitq, ← Fitq, ← Fitq, ← Fitq, fitq_flip_mirror G hp hc, fitq_flip_mirror G hp hc]
  tauto

end Hypermap

/-! ### Steps along a permutation

The number of steps from one dart to another along a permutation, the
reference's `findex`.  A dart of a face is named by the number of `face` steps
that separate it from the representative of its face that the quiz walk visits.
-/

/-- A permutation of a finite type returns to its starting point. -/
private theorem pow_minimalPeriod_self {D : Type*} (f : Equiv.Perm D) (x : D) :
    (f ^ Function.minimalPeriod f x) x = x := by
  have h := Function.isPeriodicPt_minimalPeriod (f : D → D) x
  rwa [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow] at h

/-- Every dart of a finite type is periodic, so its period is positive. -/
private theorem minimalPeriod_perm_pos {D : Type*} [Finite D] (f : Equiv.Perm D) (x : D) :
    0 < Function.minimalPeriod f x := by
  have hper : Function.IsPeriodicPt (f : D → D) (orderOf f) x := by
    change (f : D → D)^[orderOf f] x = x
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  exact hper.minimalPeriod_pos (orderOf_pos f)

/-- The number of steps from `x` to `y` along `f`, and `0` when `y` is not on
the cycle of `x`.  This is the reference's `findex`. -/
noncomputable def findex {D : Type*} (f : Equiv.Perm D) (x y : D) : ℕ :=
  sInf {n | (f ^ n) x = y}

/-- A dart is reached from itself in no steps. -/
@[simp] theorem findex_self {D : Type*} (f : Equiv.Perm D) (x : D) : findex f x x = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl (by simp))

/-- A dart on the cycle of `x` is reached in fewer steps than the length of the
cycle. -/
theorem exists_pow_lt_minimalPeriod {D : Type*} [Finite D] {f : Equiv.Perm D} {x y : D}
    (h : f.SameCycle x y) : ∃ n < Function.minimalPeriod f x, (f ^ n) x = y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨n % Function.minimalPeriod f x, Nat.mod_lt _ (minimalPeriod_perm_pos f x), ?_⟩
  have hmod := Function.iterate_mod_minimalPeriod_eq (f := (f : D → D)) (x := x) (n := n)
  rw [Equiv.Perm.iterate_eq_pow, Equiv.Perm.iterate_eq_pow] at hmod
  rw [hmod, hn]

/-- Walking `findex f x y` steps from `x` reaches `y`. -/
theorem pow_findex {D : Type*} [Finite D] {f : Equiv.Perm D} {x y : D} (h : f.SameCycle x y) :
    (f ^ findex f x y) x = y := by
  obtain ⟨n, -, hn⟩ := exists_pow_lt_minimalPeriod h
  have hne : ({m | (f ^ m) x = y} : Set ℕ).Nonempty := ⟨n, hn⟩
  exact Nat.sInf_mem hne

/-- The number of steps to a dart of the cycle of `x` is less than its length. -/
theorem findex_lt {D : Type*} [Finite D] {f : Equiv.Perm D} {x y : D} (h : f.SameCycle x y) :
    findex f x y < Function.minimalPeriod f x := by
  obtain ⟨n, hn, hxy⟩ := exists_pow_lt_minimalPeriod h
  exact lt_of_le_of_lt (Nat.sInf_le hxy) hn

/-- Below the length of the cycle, stepping and counting steps are inverse. -/
theorem findex_pow {D : Type*} [Finite D] {f : Equiv.Perm D} {x : D} {n : ℕ}
    (hn : n < Function.minimalPeriod f x) : findex f x ((f ^ n) x) = n := by
  have hsc : f.SameCycle x ((f ^ n) x) := ⟨n, by simp⟩
  have h1 : findex f x ((f ^ n) x) < Function.minimalPeriod f x := findex_lt hsc
  have h2 : (f ^ findex f x ((f ^ n) x)) x = (f ^ n) x := pow_findex hsc
  exact Function.iterate_injOn_Iio_minimalPeriod h1 hn
    (by simpa [Equiv.Perm.iterate_eq_pow] using h2)

/-- Reading a list inside its length ignores the default value. -/
private theorem getD_eq_getElem' {α : Type*} (l : List α) (d : α) {n : ℕ} (hn : n < l.length) :
    l.getD n d = l[n] := by
  simp [List.getD, List.getElem?_eq_getElem hn]

/-- Reading a concatenation just past its first part. -/
private theorem getD_append_cons {α : Type*} (l₁ l₂ : List α) (a d : α) :
    (l₁ ++ a :: l₂).getD l₁.length d = a := by
  simp [List.getD]

/-- Two lists whose images under `f` and `g` agree have matching entries. -/
private theorem getD_congr_map {α β γ : Type*} {l₁ : List α} {l₂ : List β} {f : α → γ}
    {g : β → γ} (h : l₁.map f = l₂.map g) {i : ℕ} (h₁ : i < l₁.length) (h₂ : i < l₂.length)
    (d₁ : α) (d₂ : β) : f (l₁.getD i d₁) = g (l₂.getD i d₂) := by
  rw [getD_eq_getElem' l₁ d₁ h₁, getD_eq_getElem' l₂ d₂ h₂]
  have h3 := congrArg (fun l : List γ => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at h3
  simpa using h3

namespace Hypermap

variable {D : Type*} (G : Hypermap D)

/-! ### The face projection by position

The quiz walk is face-simple, so it meets the face of a dart of the kernel in
exactly one place; `Hypermap.fidx` names that place by its position in the walk,
which is what lets the walk in the configuration map be matched with the walk in
the searched map.
-/

/-- The face test as a Boolean, for use with `List.findIdx`. -/
noncomputable def cfaceb (x y : D) : Bool := @decide (G.CFace x y) (Classical.propDecidable _)

@[simp] theorem cfaceb_eq_true {x y : D} : G.cfaceb x y = true ↔ G.CFace x y := by
  simp [cfaceb]

/-- The position in `s` of the first dart sharing a face with `x`. -/
noncomputable def fidx (s : List D) (x : D) : ℕ := s.findIdx (G.cfaceb x)

/-- A dart of the band of `s` has a position in `s`. -/
theorem fidx_lt {s : List D} {x : D} (h : G.Fband s x) : G.fidx s x < s.length := by
  obtain ⟨y, hy, hxy⟩ := h
  exact List.findIdx_lt_length_of_exists ⟨y, hy, by simpa using hxy⟩

/-- The dart of `s` at the position of `x` shares its face with `x`. -/
theorem cface_getD_fidx {s : List D} {x : D} (d : D) (h : G.Fband s x) :
    G.CFace x (s.getD (G.fidx s x) d) := by
  have hlt : s.findIdx (G.cfaceb x) < s.length := G.fidx_lt h
  have h2 : G.cfaceb x s[s.findIdx (G.cfaceb x)] = true := List.findIdx_getElem (w := hlt)
  rw [fidx, getD_eq_getElem' s d hlt]
  simpa using h2

/-- The position of a dart only depends on its face. -/
theorem fidx_congr {s : List D} {x y : D} (h : G.CFace x y) : G.fidx s x = G.fidx s y := by
  have hb : G.cfaceb x = G.cfaceb y := by
    funext z
    simp only [cfaceb, decide_eq_decide]
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  rw [fidx, fidx, hb]

/-- In a face-simple list each dart sits at its own position. -/
theorem fidx_getD {s : List D} (hs : G.Simple s) {i : ℕ} (hi : i < s.length) (d : D) :
    G.fidx s (s.getD i d) = i := by
  rw [getD_eq_getElem' s d hi]
  have hx : G.Fband s s[i] := fband_of_mem (List.getElem_mem hi)
  have hlt : G.fidx s s[i] < s.length := G.fidx_lt hx
  have hc : G.CFace s[i] (s.getD (G.fidx s s[i]) d) := G.cface_getD_fidx d hx
  rw [getD_eq_getElem' s d hlt] at hc
  have heq : s[i] = s[G.fidx s s[i]] :=
    hs.eq_of_cface (List.getElem_mem hi) (List.getElem_mem hlt) hc
  exact ((hs.nodup.getElem_inj).mp heq).symm

/-! ### Small consequences of plainness and cubicity -/

/-- The arity of a face is the length of its `face` cycle. -/
theorem arity_eq_minimalPeriod (x : D) : G.arity x = Function.minimalPeriod G.face x := rfl

/-- Arity is constant along a face. -/
theorem arity_pow_face [Finite D] (n : ℕ) (x : D) : G.arity ((G.face ^ n) x) = G.arity x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, arity_face, ih]

/-- At a dart with a three-dart node, two `node` steps are a `face` step after
an `edge` step; this is the reference's `cubic_eq'`. -/
theorem node_node_of_node3 {x : D} (h3 : G.node (G.node (G.node x)) = x) :
    G.node (G.node x) = G.face (G.edge x) := by
  have h1 : G.node (G.face (G.edge x)) = G.node (G.node (G.node x)) := by rw [G.edgeK, h3]
  exact (G.node.injective h1).symm

/-- A dart shares its face with its `face` image. -/
theorem cface_of_face_eq {x y : D} (h : G.face x = y) : G.CFace x y :=
  h ▸ Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl G.face x)

/-- Two `node` steps from a left step: this identifies the dart the doubled
left move of a question lands on. -/
theorem node_qstepL_node (hp : G.Plain) {z : D}
    (h1 : G.node (G.node (G.node z)) = z)
    (h2 : G.node (G.node (G.node (G.face (G.face (G.edge z))))) = G.face (G.face (G.edge z))) :
    G.node (G.qstepL (G.node z)) = G.face (G.face (G.edge z)) := by
  have e1 : G.node (G.node z) = G.face (G.edge z) := G.node_node_of_node3 h1
  have e2 : G.node (G.face (G.face (G.edge z))) = G.edge (G.face (G.edge z)) := hp.node_face _
  calc G.node (G.qstepL (G.node z))
      = G.node (G.node (G.edge (G.node (G.node z)))) := rfl
    _ = G.node (G.node (G.edge (G.face (G.edge z)))) := by rw [e1]
    _ = G.node (G.node (G.node (G.face (G.face (G.edge z))))) := by rw [e2]
    _ = G.face (G.face (G.edge z)) := h2

/-- A right quiz is a pair of questions that both start with a right move. -/
theorem quiz_eq_of_isQuizR {qz : Quiz} (hR : qz.IsQuizR) :
    ∃ qa₀ q₀ qa₁ q₁, qz = ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩ := by
  obtain ⟨f, s⟩ := qz
  obtain ⟨qa₀, q₀, rfl⟩ := Question.exists_of_isAskR hR.1
  obtain ⟨qa₁, q₁, rfl⟩ := Question.exists_of_isAskR hR.2
  exact ⟨qa₀, q₀, qa₁, q₁, rfl⟩

/-! ### The embedding a fitting quiz determines

A quiz valid for the configuration ring `rc` walks a transversal of the faces of
the kernel; if the same quiz also fits the searched map, the two walks can be
matched dart for dart, and this extends to a map of the whole kernel by counting
`face` steps.  This is the reference's `embedqz`.
-/

section QuizEmbedding

variable {Dm Dc : Type*} [Finite Dm] [Finite Dc]

/-- The partial map from the configuration map to the searched map that a
fitting quiz determines: the dart reached from the `i`-th dart of the
configuration walk in `k` `face` steps goes to the dart reached from the `i`-th
dart of the map walk in `k` `face` steps. -/
noncomputable def embedqz (Gm : Hypermap Dm) (Gc : Hypermap Dc) (x0c : Dc) (x0m : Dm)
    (qz : Quiz) (x : Dc) : Dm :=
  (Gm.face ^ findex Gc.face ((Gc.walkqz x0c qz).getD (Gc.fidx (Gc.walkqz x0c qz) x) x0c) x)
    ((Gm.walkqz x0m qz).getD (Gc.fidx (Gc.walkqz x0c qz) x) x0m)

variable {Gm : Hypermap Dm} {Gc : Hypermap Dc} {rc : List Dc} {x0c : Dc} {x0m : Dm} {qz : Quiz}

omit [Finite Dm] [Finite Dc] in
/-- A quiz that fits both maps matches the arities along the two walks. -/
private theorem arity_getD_eq (hqz : Gc.ValidQuiz rc x0c qz) (hfit : Gm.Fitqz x0m qz)
    {i : ℕ} (hi : i < (Gc.walkqz x0c qz).length) :
    Gm.arity ((Gm.walkqz x0m qz).getD i x0m) = Gc.arity ((Gc.walkqz x0c qz).getD i x0c) := by
  have hfc : qz.flat = (Gc.walkqz x0c qz).map Gc.arity := hqz.2.1
  have hfm : qz.flat = (Gm.walkqz x0m qz).map Gm.arity := hfit
  have hi' : i < (Gm.walkqz x0m qz).length := by simpa using hi
  exact (getD_congr_map (hfc.symm.trans hfm) hi hi' x0c x0m).symm

omit [Finite Dm] [Finite Dc] in
/-- The embedding matches the two walks position by position. -/
theorem embedqz_getD (hqz : Gc.ValidQuiz rc x0c qz) {i : ℕ}
    (hi : i < (Gc.walkqz x0c qz).length) :
    Gm.embedqz Gc x0c x0m qz ((Gc.walkqz x0c qz).getD i x0c)
      = (Gm.walkqz x0m qz).getD i x0m := by
  have hsimple : Gc.Simple (Gc.walkqz x0c qz) := hqz.2.2.1
  have hidx := Gc.fidx_getD hsimple hi x0c
  simp only [embedqz, hidx, findex_self, pow_zero]
  simp

omit [Finite Dm] [Finite Dc] in
/-- The embedding sends the base dart of the configuration to the base dart of
the map. -/
theorem embedqz_base (hqz : Gc.ValidQuiz rc x0c qz) :
    Gm.embedqz Gc x0c x0m qz x0c = x0m := by
  obtain ⟨qa₀, q₀, qa₁, q₁, rfl⟩ := quiz_eq_of_isQuizR hqz.1
  have hlt : 0 < (Gc.walkqz x0c ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩).length := by
    simp [walkqz, walkq]
  have h := embedqz_getD (Gm := Gm) (x0m := x0m) hqz hlt
  have h0c : (Gc.walkqz x0c ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩).getD 0 x0c = x0c := rfl
  have h0m : (Gm.walkqz x0m ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩).getD 0 x0m = x0m := rfl
  rwa [h0c, h0m] at h

omit [Finite Dm] [Finite Dc] in
/-- The embedding sends the other end of the base edge of the configuration to
the other end of the base edge of the map. -/
theorem embedqz_edge_base (hqz : Gc.ValidQuiz rc x0c qz) :
    Gm.embedqz Gc x0c x0m qz (Gc.edge x0c) = Gm.edge x0m := by
  obtain ⟨qa₀, q₀, qa₁, q₁, rfl⟩ := quiz_eq_of_isQuizR hqz.1
  have hc : Gc.walkqz x0c ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩ =
      (x0c :: Gc.walkq (Gc.qstepR x0c) q₀) ++
        (Gc.edge x0c :: Gc.walkq (Gc.qstepR (Gc.edge x0c)) q₁) := rfl
  have hm : Gm.walkqz x0m ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩ =
      (x0m :: Gm.walkq (Gm.qstepR x0m) q₀) ++
        (Gm.edge x0m :: Gm.walkq (Gm.qstepR (Gm.edge x0m)) q₁) := rfl
  have hlenc : (x0c :: Gc.walkq (Gc.qstepR x0c) q₀).length = q₀.flat.length + 1 := by simp
  have hlenm : (x0m :: Gm.walkq (Gm.qstepR x0m) q₀).length = q₀.flat.length + 1 := by simp
  have h0c : (Gc.walkqz x0c ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩).getD (q₀.flat.length + 1) x0c
      = Gc.edge x0c := by
    rw [hc, ← hlenc]; exact getD_append_cons _ _ _ _
  have h0m : (Gm.walkqz x0m ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩).getD (q₀.flat.length + 1) x0m
      = Gm.edge x0m := by
    rw [hm, ← hlenm]; exact getD_append_cons _ _ _ _
  have hlt : q₀.flat.length + 1 < (Gc.walkqz x0c ⟨.askR qa₀ q₀, .askR qa₁ q₁⟩).length := by
    simp [walkqz, walkq]
  have h := embedqz_getD (Gm := Gm) (x0m := x0m) hqz hlt
  rwa [h0c, h0m] at h

/-- On the kernel the embedding preserves arity. -/
theorem embedqz_arity (hqz : Gc.ValidQuiz rc x0c qz) (hfit : Gm.Fitqz x0m qz)
    {x : Dc} (hx : Gc.Kernel rc x) :
    Gm.arity (Gm.embedqz Gc x0c x0m qz x) = Gc.arity x := by
  have hbx : Gc.Fband (Gc.walkqz x0c qz) x := (hqz.2.2.2 x).mpr hx
  have hi := Gc.fidx_lt hbx
  have hcf := Gc.cface_getD_fidx (s := Gc.walkqz x0c qz) x0c hbx
  rw [embedqz, arity_pow_face, arity_getD_eq hqz hfit hi]
  exact (Gc.arity_cface hcf).symm

omit [Finite Dm] in
/-- On the kernel the embedding commutes with `face`. -/
theorem embedqz_face (hqz : Gc.ValidQuiz rc x0c qz) (hfit : Gm.Fitqz x0m qz)
    {x : Dc} (hx : Gc.Kernel rc x) :
    Gm.embedqz Gc x0c x0m qz (Gc.face x) = Gm.face (Gm.embedqz Gc x0c x0m qz x) := by
  have hbx : Gc.Fband (Gc.walkqz x0c qz) x := (hqz.2.2.2 x).mpr hx
  have hi := Gc.fidx_lt hbx
  have hxfx : Gc.CFace x (Gc.face x) :=
    Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl Gc.face x)
  have hidx : Gc.fidx (Gc.walkqz x0c qz) (Gc.face x) = Gc.fidx (Gc.walkqz x0c qz) x :=
    (Gc.fidx_congr hxfx).symm
  have hcf := Gc.cface_getD_fidx (s := Gc.walkqz x0c qz) x0c hbx
  have harity := arity_getD_eq hqz hfit hi
  simp only [embedqz, hidx]
  set y := (Gc.walkqz x0c qz).getD (Gc.fidx (Gc.walkqz x0c qz) x) x0c with hydef
  set ym := (Gm.walkqz x0m qz).getD (Gc.fidx (Gc.walkqz x0c qz) x) x0m with hymdef
  set j := findex Gc.face y x with hjdef
  have hyx : Gc.CFace y x := hcf.symm
  have hjpow : (Gc.face ^ j) y = x := pow_findex hyx
  have hjlt : j < Gc.arity y := findex_lt hyx
  have hfx : Gc.face x = (Gc.face ^ (j + 1)) y := by
    rw [pow_succ', Equiv.Perm.mul_apply, hjpow]
  have hsucc : Gm.face ((Gm.face ^ j) ym) = (Gm.face ^ (j + 1)) ym := by
    rw [pow_succ', Equiv.Perm.mul_apply]
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hjlt) with hlt | heq
  · rw [hfx, findex_pow (by rw [← arity_eq_minimalPeriod]; exact hlt), hsucc]
  · have heq' : j + 1 = Gc.arity y := heq
    have hyy : Gc.face x = y := by
      rw [hfx, heq', arity_eq_minimalPeriod]
      exact pow_minimalPeriod_self Gc.face y
    have hzero : (Gm.face ^ findex Gc.face y (Gc.face x)) ym = ym := by
      rw [hyy, findex_self]; simp
    rw [hzero, hsucc, heq', ← harity, arity_eq_minimalPeriod]
    exact (pow_minimalPeriod_self Gm.face ym).symm

/-! ### Edge-centrality along the walk

The embedding commutes with `edge` at every dart the quiz walk visits.  The
proof follows the walk: each move of a question lands on a dart whose image is
forced, and the cancellation laws then identify the two sides of the
edge-centrality equation.
-/

variable {f : Dc → Dm}

omit [Finite Dc] in
/-- The kernel is closed under `face`, so it contains `edge (node u)` whenever
it contains `u`. -/
private theorem kernel_edge_node {u : Dc} (hu : Gc.Kernel rc u) :
    Gc.Kernel rc (Gc.edge (Gc.node u)) := by
  have hk := kernel_face (G := Gc) (p := rc) (x := Gc.edge (Gc.node u))
  rw [Gc.nodeK] at hk
  exact hk.mp hu

omit [Finite Dc] in
/-- A dart of the kernel has a three-dart node. -/
private theorem node3_of_kernel (hqc : Gc.Quasicubic rc) {z : Dc} (hz : Gc.Kernel rc z) :
    Gc.node (Gc.node (Gc.node z)) = z := hqc.node_node_node (not_mem_of_kernel hz)

omit [Finite Dm] [Finite Dc] in
/-- To make `f` commute with `edge` at `v` it is enough that it does so after one
`face` step. -/
private theorem edgeCentral_of_face
    (hface : ∀ z, Gc.Kernel rc z → f (Gc.face z) = Gm.face (f z))
    {v : Dc} (hev : Gc.Kernel rc (Gc.edge v))
    (hkey : f (Gc.face (Gc.edge v)) = Gm.face (Gm.edge (f v))) :
    EdgeCentral Gc Gm f v := by
  have h1 : Gm.face (f (Gc.edge v)) = Gm.face (Gm.edge (f v)) := by
    rw [← hface _ hev, hkey]
  exact Gm.face.injective h1

omit [Finite Dm] [Finite Dc] in
/-- To make `f` commute with `edge` at `v` it is enough that it does so after two
`face` steps. -/
private theorem edgeCentral_of_face2
    (hface : ∀ z, Gc.Kernel rc z → f (Gc.face z) = Gm.face (f z))
    {v : Dc} (hev : Gc.Kernel rc (Gc.edge v)) (hfev : Gc.Kernel rc (Gc.face (Gc.edge v)))
    (hkey : f (Gc.face (Gc.face (Gc.edge v))) = Gm.face (Gm.face (Gm.edge (f v)))) :
    EdgeCentral Gc Gm f v := by
  refine edgeCentral_of_face hface hev ?_
  have h1 : Gm.face (f (Gc.face (Gc.edge v))) = Gm.face (Gm.face (Gm.edge (f v))) := by
    rw [← hface _ hfev, hkey]
  exact Gm.face.injective h1

omit [Finite Dm] [Finite Dc] in
/-- If `f` commutes with `node` at `u` then it commutes with `edge` at `node u`. -/
private theorem edgeCentral_node
    (hface : ∀ z, Gc.Kernel rc z → f (Gc.face z) = Gm.face (f z))
    {u : Dc} (hu : Gc.Kernel rc u) (hnu : f (Gc.node u) = Gm.node (f u)) :
    EdgeCentral Gc Gm f (Gc.node u) := by
  refine edgeCentral_of_face hface (kernel_edge_node hu) ?_
  rw [Gc.nodeK, hnu, Gm.nodeK]

omit [Finite Dm] [Finite Dc] in
/-- The right move: from commutation with `node` at `x` the embedding is
determined and edge-central at `edge (node x)`. -/
private theorem edgeCentral_stepR (hpm : Gm.Plain) (hpc : Gc.Plain)
    (hface : ∀ z, Gc.Kernel rc z → f (Gc.face z) = Gm.face (f z))
    {x : Dc} (hx : Gc.Kernel rc x) (hnx : Gc.Kernel rc (Gc.node x))
    (hhn : f (Gc.node x) = Gm.node (f x)) :
    f (Gc.edge (Gc.node x)) = Gm.edge (Gm.node (f x)) ∧
      Gc.Kernel rc (Gc.edge (Gc.node x)) ∧
      Gc.Kernel rc (Gc.edge (Gc.edge (Gc.node x))) ∧
      EdgeCentral Gc Gm f (Gc.edge (Gc.node x)) := by
  have hcn : EdgeCentral Gc Gm f (Gc.node x) := edgeCentral_node hface hx hhn
  have hcn' : f (Gc.edge (Gc.node x)) = Gm.edge (f (Gc.node x)) := hcn
  refine ⟨by rw [hcn', hhn], kernel_edge_node hx, ?_,
    (edgeCentral_edge hpc hpm (Gc.node x)).mpr hcn⟩
  rw [hpc.edge_edge]
  exact hnx

omit [Finite Dm] [Finite Dc] in
/-- The left move: from commutation with `node` at `x` the embedding is
determined and edge-central at `edge (node (node x))`. -/
private theorem edgeCentral_stepL (hpm : Gm.Plain) (hcm : Gm.Cubic) (hpc : Gc.Plain)
    (hqc : Gc.Quasicubic rc)
    (hface : ∀ z, Gc.Kernel rc z → f (Gc.face z) = Gm.face (f z))
    {x : Dc} (hx : Gc.Kernel rc x) (hex : Gc.Kernel rc (Gc.edge x))
    (hnx : Gc.Kernel rc (Gc.node x)) (hc : EdgeCentral Gc Gm f x)
    (hhn : f (Gc.node x) = Gm.node (f x)) :
    f (Gc.edge (Gc.node (Gc.node x))) = Gm.edge (Gm.node (Gm.node (f x))) ∧
      Gc.Kernel rc (Gc.edge (Gc.node (Gc.node x))) ∧
      Gc.Kernel rc (Gc.edge (Gc.edge (Gc.node (Gc.node x)))) ∧
      EdgeCentral Gc Gm f (Gc.edge (Gc.node (Gc.node x))) := by
  have hc' : f (Gc.edge x) = Gm.edge (f x) := hc
  have hK1 : Gc.Kernel rc (Gc.edge (Gc.node (Gc.node x))) := kernel_edge_node hnx
  have hnn : Gc.node (Gc.node x) = Gc.face (Gc.edge x) :=
    Gc.node_node_of_node3 (node3_of_kernel hqc hx)
  have hK2 : Gc.Kernel rc (Gc.edge (Gc.edge (Gc.node (Gc.node x)))) := by
    rw [hpc.edge_edge, hnn]
    exact kernel_face.mpr hex
  have hval : f (Gc.edge (Gc.node (Gc.node x))) = Gm.edge (Gm.node (Gm.node (f x))) := by
    refine Gm.face.injective ?_
    rw [← hface _ hK1, Gc.nodeK, hhn, Gm.nodeK]
  refine ⟨hval, hK1, hK2, ?_⟩
  change f (Gc.edge (Gc.edge (Gc.node (Gc.node x)))) = Gm.edge (f (Gc.edge (Gc.node (Gc.node x))))
  rw [hval, hpm.edge_edge, hpc.edge_edge, hnn, hface _ hex, hc', hcm.node_node]

omit [Finite Dm] [Finite Dc] in
/-- The darts a question visits from `node x` are edge-central as soon as they
lie in the kernel and the embedding matches the two walks.  This is the
induction at the heart of the reference's `embedqz_central`. -/
private theorem edgeCentral_walkq (hpm : Gm.Plain) (hcm : Gm.Cubic) (hpc : Gc.Plain)
    (hqc : Gc.Quasicubic rc)
    (hface : ∀ z, Gc.Kernel rc z → f (Gc.face z) = Gm.face (f z)) :
    ∀ (q : Question) (x : Dc), Gc.Kernel rc x → Gc.Kernel rc (Gc.edge x) →
      EdgeCentral Gc Gm f x →
      (∀ y ∈ Gc.walkq (Gc.node x) q, Gc.Kernel rc y) →
      (Gc.walkq (Gc.node x) q).map f = Gm.walkq (Gm.node (f x)) q →
      ∀ y ∈ Gc.walkq (Gc.node x) q, EdgeCentral Gc Gm f y := by
  intro q
  induction q with
  | ask0 => intro x _ _ _ _ _ y hy; simp [walkq] at hy
  | ask1 qa =>
    intro x hx _ _ _ hmap y hy
    simp only [walkq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
    simp only [walkq, List.mem_singleton] at hy
    subst hy
    exact edgeCentral_node hface hx hmap
  | askL qa ql ih =>
    intro x hx hex hc hker hmap y hy
    have hwalk : Gc.walkq (Gc.node x) (.askL qa ql)
        = Gc.node x :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql := rfl
    have hwalkm : Gm.walkq (Gm.node (f x)) (.askL qa ql)
        = Gm.node (f x) :: Gm.walkq (Gm.node (Gm.edge (Gm.node (Gm.node (f x))))) ql := rfl
    rw [hwalk] at hker hmap hy
    rw [hwalkm, List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hhn, hmap'⟩ := hmap
    have hnx : Gc.Kernel rc (Gc.node x) := hker _ (by simp)
    obtain ⟨hval, hK1, hK2, hcen⟩ :=
      edgeCentral_stepL hpm hcm hpc hqc hface hx hex hnx hc hhn
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact edgeCentral_node hface hx hhn
    · refine ih _ hK1 hK2 hcen (fun z hz => hker z (List.mem_cons_of_mem _ hz)) ?_ _ hy'
      rw [hval]
      exact hmap'
  | askR qa qr ih =>
    intro x hx hex hc hker hmap y hy
    have hwalk : Gc.walkq (Gc.node x) (.askR qa qr)
        = Gc.node x :: Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr := rfl
    have hwalkm : Gm.walkq (Gm.node (f x)) (.askR qa qr)
        = Gm.node (f x) :: Gm.walkq (Gm.node (Gm.edge (Gm.node (f x)))) qr := rfl
    rw [hwalk] at hker hmap hy
    rw [hwalkm, List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hhn, hmap'⟩ := hmap
    have hnx : Gc.Kernel rc (Gc.node x) := hker _ (by simp)
    obtain ⟨hval, hK1, hK2, hcen⟩ := edgeCentral_stepR hpm hpc hface hx hnx hhn
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact edgeCentral_node hface hx hhn
    · refine ih _ hK1 hK2 hcen (fun z hz => hker z (List.mem_cons_of_mem _ hz)) ?_ _ hy'
      rw [hval]
      exact hmap'
  | askLR qa ql qr ihl ihr =>
    intro x hx hex hc hker hmap y hy
    have hwalk : Gc.walkq (Gc.node x) (.askLR qa ql qr)
        = Gc.node x :: (Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql
            ++ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr) := rfl
    have hwalkm : Gm.walkq (Gm.node (f x)) (.askLR qa ql qr)
        = Gm.node (f x) :: (Gm.walkq (Gm.node (Gm.edge (Gm.node (Gm.node (f x))))) ql
            ++ Gm.walkq (Gm.node (Gm.edge (Gm.node (f x)))) qr) := rfl
    rw [hwalk] at hker hmap hy
    rw [hwalkm, List.map_cons, List.map_append, List.cons.injEq] at hmap
    obtain ⟨hhn, happ⟩ := hmap
    have hlen : ((Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql).map f).length
        = (Gm.walkq (Gm.node (Gm.edge (Gm.node (Gm.node (f x))))) ql).length := by simp
    obtain ⟨hmapl, hmapr⟩ := (append_eq_append_iff_of_length hlen).mp happ
    have hnx : Gc.Kernel rc (Gc.node x) := hker _ (by simp)
    have hkerl : ∀ z ∈ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql,
        Gc.Kernel rc z := fun z hz =>
      hker z (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
    have hkerr : ∀ z ∈ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr,
        Gc.Kernel rc z := fun z hz =>
      hker z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))
    obtain ⟨hvalL, hK1L, hK2L, hcenL⟩ :=
      edgeCentral_stepL hpm hcm hpc hqc hface hx hex hnx hc hhn
    obtain ⟨hvalR, hK1R, hK2R, hcenR⟩ := edgeCentral_stepR hpm hpc hface hx hnx hhn
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact edgeCentral_node hface hx hhn
    · rcases List.mem_append.mp hy' with hyl | hyr
      · refine ihl _ hK1L hK2L hcenL hkerl ?_ _ hyl
        rw [hvalL]
        exact hmapl
      · refine ihr _ hK1R hK2R hcenR hkerr ?_ _ hyr
        rw [hvalR]
        exact hmapr
  | askLL qa qll ih =>
    intro x hx hex hc hker hmap y hy
    have hc' : f (Gc.edge x) = Gm.edge (f x) := hc
    have hK_fex : Gc.Kernel rc (Gc.face (Gc.edge x)) := kernel_face.mpr hex
    have hK_ffex : Gc.Kernel rc (Gc.face (Gc.face (Gc.edge x))) := kernel_face.mpr hK_fex
    have hDc : Gc.node (Gc.qstepL (Gc.node x)) = Gc.face (Gc.face (Gc.edge x)) :=
      Gc.node_qstepL_node hpc (node3_of_kernel hqc hx) (node3_of_kernel hqc hK_ffex)
    have hDm : Gm.node (Gm.qstepL (Gm.node (f x))) = Gm.face (Gm.face (Gm.edge (f x))) :=
      Gm.node_qstepL_node hpm (hcm.node_node_node _) (hcm.node_node_node _)
    have hwalk : Gc.walkq (Gc.node x) (.askLL qa qll)
        = Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))
            :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))) qll := rfl
    have hwalkm : Gm.walkq (Gm.node (f x)) (.askLL qa qll)
        = Gm.edge (Gm.node (Gm.qstepL (Gm.node (f x))))
            :: Gm.walkq (Gm.node (Gm.edge (Gm.node (Gm.qstepL (Gm.node (f x)))))) qll := rfl
    rw [hwalk] at hker hmap hy
    rw [hwalkm, List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hfw, hmap'⟩ := hmap
    have hKw : Gc.Kernel rc (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))) := hker _ (by simp)
    have hew : Gc.edge (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))
        = Gc.face (Gc.face (Gc.edge x)) := by rw [hpc.edge_edge, hDc]
    have hKew : Gc.Kernel rc (Gc.edge (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))) := by
      rw [hew]; exact hK_ffex
    have hcw : EdgeCentral Gc Gm f (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))) := by
      change f (Gc.edge (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))))
        = Gm.edge (f (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))))
      rw [hew, hface _ hK_fex, hface _ hex, hc', hfw, hpm.edge_edge, hDm]
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hcw
    · refine ih _ hKw hKew hcw (fun z hz => hker z (List.mem_cons_of_mem _ hz)) ?_ _ hy'
      rw [hfw]
      exact hmap'
  | askRR qa qrr ih =>
    intro x hx hex hc hker hmap y hy
    have hwalk : Gc.walkq (Gc.node x) (.askRR qa qrr)
        = Gc.node (Gc.edge (Gc.node x))
            :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.edge (Gc.node x))))) qrr := rfl
    have hwalkm : Gm.walkq (Gm.node (f x)) (.askRR qa qrr)
        = Gm.node (Gm.edge (Gm.node (f x)))
            :: Gm.walkq (Gm.node (Gm.edge (Gm.node (Gm.edge (Gm.node (f x)))))) qrr := rfl
    rw [hwalk] at hker hmap hy
    rw [hwalkm, List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hfv, hmap'⟩ := hmap
    have hKen : Gc.Kernel rc (Gc.edge (Gc.node x)) := kernel_edge_node hx
    have hKev : Gc.Kernel rc (Gc.edge (Gc.node (Gc.edge (Gc.node x)))) :=
      kernel_edge_node hKen
    have hfev : Gc.face (Gc.edge (Gc.node (Gc.edge (Gc.node x)))) = Gc.edge (Gc.node x) :=
      Gc.nodeK _
    have hcv : EdgeCentral Gc Gm f (Gc.node (Gc.edge (Gc.node x))) := by
      refine edgeCentral_of_face2 hface hKev (by rw [hfev]; exact hKen) ?_
      rw [hfev, Gc.nodeK, hfv, Gm.nodeK, Gm.nodeK]
    have hcv' : f (Gc.edge (Gc.node (Gc.edge (Gc.node x))))
        = Gm.edge (f (Gc.node (Gc.edge (Gc.node x)))) := hcv
    have hKv : Gc.Kernel rc (Gc.node (Gc.edge (Gc.node x))) := hker _ (by simp)
    have hKeev : Gc.Kernel rc (Gc.edge (Gc.edge (Gc.node (Gc.edge (Gc.node x))))) := by
      rw [hpc.edge_edge]; exact hKv
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hcv
    · refine ih _ hKev hKeev ((edgeCentral_edge hpc hpm _).mpr hcv)
        (fun z hz => hker z (List.mem_cons_of_mem _ hz)) ?_ _ hy'
      rw [hcv', hfv]
      exact hmap'

omit [Finite Dm] in
/-- **Every dart of the configuration walk is edge-central.**  This is the
reference's `embedqz_central`. -/
theorem embedqz_central (hpm : Gm.Plain) (hcm : Gm.Cubic) (hpc : Gc.Plain)
    (hqc : Gc.Quasicubic rc) (hqz : Gc.ValidQuiz rc x0c qz) (hfit : Gm.Fitqz x0m qz)
    {y : Dc} (hy : y ∈ Gc.walkqz x0c qz) :
    EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) y := by
  have hface : ∀ z, Gc.Kernel rc z →
      Gm.embedqz Gc x0c x0m qz (Gc.face z) = Gm.face (Gm.embedqz Gc x0c x0m qz z) :=
    fun z hz => embedqz_face hqz hfit hz
  have hker : ∀ z ∈ Gc.walkqz x0c qz, Gc.Kernel rc z :=
    fun z hz => (hqz.2.2.2 z).mp (fband_of_mem hz)
  have hmapeq : (Gc.walkqz x0c qz).map (Gm.embedqz Gc x0c x0m qz) = Gm.walkqz x0m qz := by
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    rw [List.getElem_map]
    have hi : i < (Gc.walkqz x0c qz).length := by simpa using h1
    have hg := embedqz_getD (Gm := Gm) (x0m := x0m) hqz hi
    rwa [getD_eq_getElem' _ _ hi, getD_eq_getElem' _ _ h2] at hg
  have hbase : Gm.embedqz Gc x0c x0m qz x0c = x0m := embedqz_base hqz
  have hebase : Gm.embedqz Gc x0c x0m qz (Gc.edge x0c) = Gm.edge x0m := embedqz_edge_base hqz
  have hc0 : EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) x0c := by
    change Gm.embedqz Gc x0c x0m qz (Gc.edge x0c) = Gm.edge (Gm.embedqz Gc x0c x0m qz x0c)
    rw [hebase, hbase]
  have hce0 : EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) (Gc.edge x0c) :=
    (edgeCentral_edge hpc hpm x0c).mpr hc0
  obtain ⟨qa₀, q₀, qa₁, q₁, hqzeq⟩ := quiz_eq_of_isQuizR hqz.1
  have hsplitc : Gc.walkqz x0c qz
      = (x0c :: Gc.walkq (Gc.node (Gc.edge x0c)) q₀)
        ++ (Gc.edge x0c :: Gc.walkq (Gc.node (Gc.edge (Gc.edge x0c))) q₁) := by
    rw [hqzeq]; rfl
  have hsplitm : Gm.walkqz x0m qz
      = (x0m :: Gm.walkq (Gm.node (Gm.edge x0m)) q₀)
        ++ (Gm.edge x0m :: Gm.walkq (Gm.node (Gm.edge (Gm.edge x0m))) q₁) := by
    rw [hqzeq]; rfl
  rw [hsplitc] at hker hy hmapeq
  rw [hsplitm] at hmapeq
  rw [List.map_append, List.map_cons, List.map_cons] at hmapeq
  have hlen : ((Gm.embedqz Gc x0c x0m qz x0c)
      :: (Gc.walkq (Gc.node (Gc.edge x0c)) q₀).map (Gm.embedqz Gc x0c x0m qz)).length
      = (x0m :: Gm.walkq (Gm.node (Gm.edge x0m)) q₀).length := by simp
  obtain ⟨hm₀, hm₁⟩ := (append_eq_append_iff_of_length hlen).mp hmapeq
  rw [List.cons.injEq] at hm₀ hm₁
  have hK0 : Gc.Kernel rc x0c := hker _ (by simp)
  have hKe0 : Gc.Kernel rc (Gc.edge x0c) := hker _ (by simp)
  -- the first question is asked from the other end of the base edge
  have hstep₀ : ∀ z ∈ Gc.walkq (Gc.node (Gc.edge x0c)) q₀,
      EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z := by
    refine edgeCentral_walkq hpm hcm hpc hqc hface q₀ (Gc.edge x0c) hKe0 ?_ hce0 ?_ ?_
    · rw [hpc.edge_edge]; exact hK0
    · exact fun z hz => hker z (by simp [hz])
    · rw [hebase]
      exact hm₀.2
  -- the second question is asked from the base dart
  have hstep₁ : ∀ z ∈ Gc.walkq (Gc.node x0c) q₁,
      EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z := by
    refine edgeCentral_walkq hpm hcm hpc hqc hface q₁ x0c hK0 hKe0 hc0 ?_ ?_
    · intro z hz
      refine hker z ?_
      simp only [List.cons_append, List.mem_cons, List.mem_append, hpc.edge_edge] at hz ⊢
      exact Or.inr (Or.inr (Or.inr hz))
    · rw [hbase]
      have := hm₁.2
      rw [hpc.edge_edge] at this
      rw [this, hpm.edge_edge]
  rcases List.mem_append.mp hy with hy' | hy'
  · rcases List.mem_cons.mp hy' with rfl | hy''
    · exact hc0
    · exact hstep₀ _ hy''
  · rcases List.mem_cons.mp hy' with rfl | hy''
    · exact hce0
    · rw [hpc.edge_edge] at hy''
      exact hstep₁ _ hy''

/-! ### R-connectivity of the edge-central kernel

The kernel is covered by the faces the quiz walk visits, and the walk builds
that cover one dart at a time.  Each dart added is a `node` image of a dart
already covered, and adding such a dart keeps the covered region R-connected.
-/

omit [Finite Dc] in
/-- Transporting R-connectivity along an equality of sets. -/
private theorem rlinkConnected_congr {A B : Set Dc} (hAB : A = B)
    (h : Gc.RlinkConnected A) : Gc.RlinkConnected B := hAB ▸ h

omit [Finite Dc] in
/-- Adding the `node` image of a covered dart keeps the covered region
R-connected.  This is the reference's `ccRfband`. -/
private theorem rlinkConnected_fband_snoc (hpc : Gc.Plain) {P : Dc → Prop}
    (hP : ∀ z, P (Gc.edge z) ↔ P z) {a : List Dc} {x : Dc} (hx : Gc.Fband a x)
    (hcc : Gc.RlinkConnected {z | Gc.Fband a z ∧ P z}) (hnx : P (Gc.node x)) :
    Gc.RlinkConnected {z | Gc.Fband (a ++ [Gc.node x]) z ∧ P z} := by
  have hea : Gc.Fband a (Gc.edge (Gc.node x)) := by
    have h1 : Gc.Fband a (Gc.face (Gc.edge (Gc.node x))) := by rw [Gc.nodeK]; exact hx
    rwa [fband_face] at h1
  have heP : P (Gc.edge (Gc.node x)) := (hP _).mpr hnx
  have hmem : ∀ z, Gc.Fband a z ∧ P z → Gc.Fband (a ++ [Gc.node x]) z ∧ P z :=
    fun z hz => ⟨fband_concat.mpr (Or.inr hz.1), hz.2⟩
  intro u hu v hv
  obtain ⟨hub, hup⟩ := hu
  obtain ⟨hvb, hvp⟩ := hv
  rw [fband_concat] at hub hvb
  by_cases hun : Gc.CFace u (Gc.node x)
  · by_cases hvn : Gc.CFace v (Gc.node x)
    · refine ⟨[], List.IsChain.cons_cons ?_ (List.IsChain.singleton v), by simp⟩
      change Gc.CFace (Gc.edge (Gc.node (Gc.face u))) v
      rw [Gc.faceK]
      exact hun.trans hvn.symm
    · obtain ⟨p, hchain, hpA⟩ := hcc _ ⟨hea, heP⟩ v ⟨hvb.resolve_left hvn, hvp⟩
      rw [Gc.edgeK] at hchain
      refine ⟨Gc.node x :: p, List.IsChain.cons_cons ?_ hchain, ?_⟩
      · change Gc.CFace (Gc.edge (Gc.node (Gc.face u))) (Gc.node x)
        rw [Gc.faceK]
        exact hun
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact ⟨fband_concat.mpr (Or.inl (Equiv.Perm.SameCycle.refl _ _)), hnx⟩
        · exact hmem z (hpA z hz')
  · by_cases hvn : Gc.CFace v (Gc.node x)
    · obtain ⟨p, hchain, hpA⟩ := hcc u ⟨hub.resolve_left hun, hup⟩ _ ⟨hea, heP⟩
      refine ⟨p ++ [Gc.edge (Gc.node x)], ?_, ?_⟩
      · have hstep : Gc.Rlink
            ((p ++ [Gc.edge (Gc.node x)]).getLastD (Gc.node (Gc.face u))) v := by
          rw [getLastD_append_cons]
          change Gc.CFace (Gc.edge (Gc.edge (Gc.node x))) v
          rw [hpc.edge_edge]
          exact hvn.symm
        exact isChain_append_cons hchain hstep (List.IsChain.singleton v)
      · intro z hz
        rcases List.mem_append.mp hz with hz' | hz'
        · exact hmem z (hpA z hz')
        · rw [List.mem_singleton] at hz'
          subst hz'
          exact ⟨fband_concat.mpr (Or.inr hea), heP⟩
    · obtain ⟨p, hchain, hpA⟩ :=
        hcc u ⟨hub.resolve_left hun, hup⟩ v ⟨hvb.resolve_left hvn, hvp⟩
      exact ⟨p, hchain, fun z hz => hmem z (hpA z hz)⟩

omit [Finite Dc] in
/-- Walking a question keeps the covered region R-connected.  This is the
reference's `ccRwalk`. -/
private theorem rlinkConnected_fband_walkq (hpc : Gc.Plain) (hqc : Gc.Quasicubic rc)
    {P : Dc → Prop} (hP : ∀ z, P (Gc.edge z) ↔ P z) :
    ∀ (q : Question) (x : Dc) (a : List Dc), Gc.Fband a x → Gc.Fband a (Gc.edge x) →
      (∀ z ∈ a, Gc.Kernel rc z) → Gc.RlinkConnected {z | Gc.Fband a z ∧ P z} →
      (∀ z ∈ Gc.walkq (Gc.node x) q, Gc.Kernel rc z ∧ P z) →
      Gc.RlinkConnected {z | Gc.Fband (a ++ Gc.walkq (Gc.node x) q) z ∧ P z} := by
  intro q
  induction q with
  | ask0 =>
    intro x a _ _ _ hcc _
    rw [show Gc.walkq (Gc.node x) Question.ask0 = [] from rfl, List.append_nil]
    exact hcc
  | ask1 qa =>
    intro x a hax _ haker hcc hwk
    have hwk' : ∀ z ∈ [Gc.node x], Gc.Kernel rc z ∧ P z := hwk
    rw [show a ++ Gc.walkq (Gc.node x) (Question.ask1 qa) = a ++ [Gc.node x] from rfl]
    exact rlinkConnected_fband_snoc hpc hP hax hcc (hwk' (Gc.node x) (by simp)).2
  | askL qa ql ih =>
    intro x a hax haex haker hcc hwk
    have hwk' : ∀ z ∈ Gc.node x :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql,
        Gc.Kernel rc z ∧ P z := hwk
    have hnx := hwk' (Gc.node x) (by simp)
    have hxk : Gc.Kernel rc x := by
      obtain ⟨w, hw, hxw⟩ := hax
      exact (Kernel.congr hxw).mpr (haker w hw)
    have hnn : Gc.node (Gc.node x) = Gc.face (Gc.edge x) :=
      Gc.node_node_of_node3 (node3_of_kernel hqc hxk)
    have hcc' : Gc.RlinkConnected {z | Gc.Fband (a ++ [Gc.node x]) z ∧ P z} :=
      rlinkConnected_fband_snoc hpc hP hax hcc hnx.2
    have hlist : a ++ Gc.walkq (Gc.node x) (Question.askL qa ql)
        = (a ++ [Gc.node x]) ++ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql := by
      change a ++ (Gc.node x :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql) = _
      simp
    rw [hlist]
    refine ih _ _ ?_ ?_ ?_ hcc' (fun z hz => hwk' z (List.mem_cons_of_mem _ hz))
    · exact fband_concat.mpr (Or.inl (Gc.cface_of_face_eq (Gc.nodeK _)))
    · refine fband_concat.mpr (Or.inr ?_)
      rw [hpc.edge_edge, hnn, fband_face]
      exact haex
    · intro z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · exact haker z hz'
      · rw [List.mem_singleton] at hz'
        subst hz'
        exact hnx.1
  | askR qa qr ih =>
    intro x a hax haex haker hcc hwk
    have hwk' : ∀ z ∈ Gc.node x :: Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr,
        Gc.Kernel rc z ∧ P z := hwk
    have hnx := hwk' (Gc.node x) (by simp)
    have hcc' : Gc.RlinkConnected {z | Gc.Fband (a ++ [Gc.node x]) z ∧ P z} :=
      rlinkConnected_fband_snoc hpc hP hax hcc hnx.2
    have hlist : a ++ Gc.walkq (Gc.node x) (Question.askR qa qr)
        = (a ++ [Gc.node x]) ++ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr := by
      change a ++ (Gc.node x :: Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr) = _
      simp
    rw [hlist]
    refine ih _ _ ?_ ?_ ?_ hcc' (fun z hz => hwk' z (List.mem_cons_of_mem _ hz))
    · refine fband_concat.mpr (Or.inr ?_)
      rw [← fband_face, Gc.nodeK]
      exact hax
    · exact fband_concat.mpr (Or.inl (by rw [hpc.edge_edge]))
    · intro z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · exact haker z hz'
      · rw [List.mem_singleton] at hz'
        subst hz'
        exact hnx.1
  | askLR qa ql qr ihl ihr =>
    intro x a hax haex haker hcc hwk
    have hwk' : ∀ z ∈ Gc.node x :: (Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql
        ++ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr), Gc.Kernel rc z ∧ P z := hwk
    have hnx := hwk' (Gc.node x) (by simp)
    have hxk : Gc.Kernel rc x := by
      obtain ⟨w, hw, hxw⟩ := hax
      exact (Kernel.congr hxw).mpr (haker w hw)
    have hnn : Gc.node (Gc.node x) = Gc.face (Gc.edge x) :=
      Gc.node_node_of_node3 (node3_of_kernel hqc hxk)
    have hcc' : Gc.RlinkConnected {z | Gc.Fband (a ++ [Gc.node x]) z ∧ P z} :=
      rlinkConnected_fband_snoc hpc hP hax hcc hnx.2
    have hakerL : ∀ z ∈ (a ++ [Gc.node x]), Gc.Kernel rc z := by
      intro z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · exact haker z hz'
      · rw [List.mem_singleton] at hz'; subst hz'; exact hnx.1
    have hccL : Gc.RlinkConnected
        {z | Gc.Fband ((a ++ [Gc.node x])
          ++ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql) z ∧ P z} := by
      refine ihl _ _ ?_ ?_ hakerL hcc' ?_
      · exact fband_concat.mpr (Or.inl (Gc.cface_of_face_eq (Gc.nodeK _)))
      · refine fband_concat.mpr (Or.inr ?_)
        rw [hpc.edge_edge, hnn, fband_face]
        exact haex
      · exact fun z hz => hwk' z (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
    have hlist : a ++ Gc.walkq (Gc.node x) (Question.askLR qa ql qr)
        = ((a ++ [Gc.node x]) ++ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql)
          ++ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr := by
      change a ++ (Gc.node x :: (Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql
        ++ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr)) = _
      simp
    rw [hlist]
    refine ihr _ _ ?_ ?_ ?_ hccL
      (fun z hz => hwk' z (List.mem_cons_of_mem _ (List.mem_append_right _ hz)))
    · refine fband_append.mpr (Or.inl (fband_concat.mpr (Or.inr ?_)))
      rw [← fband_face, Gc.nodeK]
      exact hax
    · exact fband_append.mpr (Or.inl (fband_concat.mpr (Or.inl (by rw [hpc.edge_edge]))))
    · intro z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · exact hakerL z hz'
      · exact (hwk' z (List.mem_cons_of_mem _ (List.mem_append_left _ hz'))).1
  | askLL qa qll ih =>
    intro x a hax haex haker hcc hwk
    have hwk' : ∀ z ∈ Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))
        :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))) qll,
        Gc.Kernel rc z ∧ P z := hwk
    have hw := hwk' (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))) (by simp)
    have hxk : Gc.Kernel rc x := by
      obtain ⟨w, hw', hxw⟩ := hax
      exact (Kernel.congr hxw).mpr (haker w hw')
    have hexk : Gc.Kernel rc (Gc.edge x) := by
      obtain ⟨w, hw', hxw⟩ := haex
      exact (Kernel.congr hxw).mpr (haker w hw')
    have hffk : Gc.Kernel rc (Gc.face (Gc.face (Gc.edge x))) :=
      kernel_face.mpr (kernel_face.mpr hexk)
    have hD : Gc.node (Gc.qstepL (Gc.node x)) = Gc.face (Gc.face (Gc.edge x)) :=
      Gc.node_qstepL_node hpc (node3_of_kernel hqc hxk) (node3_of_kernel hqc hffk)
    have hffb : Gc.Fband a (Gc.face (Gc.face (Gc.edge x))) := by
      rw [fband_face, fband_face]; exact haex
    have hwnode : Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))
        = Gc.node (Gc.face (Gc.face (Gc.face (Gc.edge x)))) := by
      rw [hpc.node_face, hD]
    have hcc' : Gc.RlinkConnected
        {z | Gc.Fband (a ++ [Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))]) z ∧ P z} := by
      rw [hwnode]
      refine rlinkConnected_fband_snoc hpc hP ?_ hcc ?_
      · rw [fband_face]; exact hffb
      · rw [← hwnode]; exact hw.2
    have hlist : a ++ Gc.walkq (Gc.node x) (Question.askLL qa qll)
        = (a ++ [Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))])
          ++ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))) qll := by
      change a ++ (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))
        :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))) qll) = _
      simp
    rw [hlist]
    refine ih _ _ ?_ ?_ ?_ hcc' (fun z hz => hwk' z (List.mem_cons_of_mem _ hz))
    · exact fband_concat.mpr (Or.inl (Equiv.Perm.SameCycle.refl _ _))
    · refine fband_concat.mpr (Or.inr ?_)
      rw [hpc.edge_edge, hD]
      exact hffb
    · intro z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · exact haker z hz'
      · rw [List.mem_singleton] at hz'; subst hz'; exact hw.1
  | askRR qa qrr ih =>
    intro x a hax haex haker hcc hwk
    have hwk' : ∀ z ∈ Gc.node (Gc.edge (Gc.node x))
        :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.edge (Gc.node x))))) qrr,
        Gc.Kernel rc z ∧ P z := hwk
    have hv := hwk' (Gc.node (Gc.edge (Gc.node x))) (by simp)
    have henb : Gc.Fband a (Gc.edge (Gc.node x)) := by
      rw [← fband_face, Gc.nodeK]; exact hax
    have hcc' : Gc.RlinkConnected
        {z | Gc.Fband (a ++ [Gc.node (Gc.edge (Gc.node x))]) z ∧ P z} :=
      rlinkConnected_fband_snoc hpc hP henb hcc hv.2
    have hlist : a ++ Gc.walkq (Gc.node x) (Question.askRR qa qrr)
        = (a ++ [Gc.node (Gc.edge (Gc.node x))])
          ++ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.edge (Gc.node x))))) qrr := by
      change a ++ (Gc.node (Gc.edge (Gc.node x))
        :: Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.edge (Gc.node x))))) qrr) = _
      simp
    rw [hlist]
    refine ih _ _ ?_ ?_ ?_ hcc' (fun z hz => hwk' z (List.mem_cons_of_mem _ hz))
    · refine fband_concat.mpr (Or.inr ?_)
      rw [← fband_face, Gc.nodeK]
      exact henb
    · exact fband_concat.mpr (Or.inl (by rw [hpc.edge_edge]))
    · intro z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · exact haker z hz'
      · rw [List.mem_singleton] at hz'; subst hz'; exact hv.1

omit [Finite Dm] in
/-- **The edge-central darts of the kernel are R-connected.**  This is the
reference's `embedqz_rlinked`. -/
theorem embedqz_rlinked (hpm : Gm.Plain) (hcm : Gm.Cubic) (hpc : Gc.Plain)
    (hqc : Gc.Quasicubic rc) (hqz : Gc.ValidQuiz rc x0c qz) (hfit : Gm.Fitqz x0m qz) :
    Gc.RlinkConnected
      {z | Gc.Kernel rc z ∧ EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z} := by
  have hP : ∀ z, EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) (Gc.edge z) ↔
      EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z := fun z => edgeCentral_edge hpc hpm z
  obtain ⟨qa₀, q₀, qa₁, q₁, hqzeq⟩ := quiz_eq_of_isQuizR hqz.1
  have hsplitc : Gc.walkqz x0c qz
      = (x0c :: Gc.walkq (Gc.node (Gc.edge x0c)) q₀)
        ++ (Gc.edge x0c :: Gc.walkq (Gc.node (Gc.edge (Gc.edge x0c))) q₁) := by
    rw [hqzeq]; rfl
  have hker : ∀ z ∈ Gc.walkqz x0c qz, Gc.Kernel rc z :=
    fun z hz => (hqz.2.2.2 z).mp (fband_of_mem hz)
  have hcen : ∀ z ∈ Gc.walkqz x0c qz, EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z :=
    fun z hz => embedqz_central hpm hcm hpc hqc hqz hfit hz
  have hwk : ∀ z ∈ Gc.walkqz x0c qz,
      Gc.Kernel rc z ∧ EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z :=
    fun z hz => ⟨hker z hz, hcen z hz⟩
  rw [hsplitc] at hwk
  have hK0 : Gc.Kernel rc x0c ∧ EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) x0c :=
    hwk x0c (by simp)
  have hKe0 : Gc.Kernel rc (Gc.edge x0c) ∧
      EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) (Gc.edge x0c) := hwk (Gc.edge x0c) (by simp)
  -- the two base darts
  have hbase : Gc.RlinkConnected
      {z | Gc.Fband [x0c] z ∧ EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z} := by
    intro u hu v hv
    refine ⟨[], List.IsChain.cons_cons ?_ (List.IsChain.singleton v), by simp⟩
    change Gc.CFace (Gc.edge (Gc.node (Gc.face u))) v
    rw [Gc.faceK]
    obtain ⟨hub, -⟩ := hu
    obtain ⟨hvb, -⟩ := hv
    simp only [fband_cons, fband_nil, or_false] at hub hvb
    exact hub.trans hvb.symm
  have hbase2 : Gc.RlinkConnected
      {z | Gc.Fband [x0c, Gc.edge x0c] z ∧
        EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z} := by
    have hlist : [x0c, Gc.edge x0c] = [x0c] ++ [Gc.node (Gc.face x0c)] := by
      rw [hpc.node_face]; simp
    rw [hlist]
    refine rlinkConnected_fband_snoc hpc hP ?_ hbase ?_
    · exact ⟨x0c, by simp,
        (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl Gc.face x0c)).symm⟩
    · rw [hpc.node_face]; exact hKe0.2
  have haker : ∀ z ∈ [x0c, Gc.edge x0c], Gc.Kernel rc z := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hK0.1
    · rw [List.mem_singleton] at hz'; subst hz'; exact hKe0.1
  -- the first question, asked from the other end of the base edge
  have hcc₁ : Gc.RlinkConnected
      {z | Gc.Fband ([x0c, Gc.edge x0c] ++ Gc.walkq (Gc.node (Gc.edge x0c)) q₀) z ∧
        EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z} := by
    refine rlinkConnected_fband_walkq hpc hqc hP q₀ (Gc.edge x0c) _ ?_ ?_ haker
      hbase2 ?_
    · exact ⟨Gc.edge x0c, by simp, Equiv.Perm.SameCycle.refl _ _⟩
    · rw [hpc.edge_edge]
      exact ⟨x0c, by simp, Equiv.Perm.SameCycle.refl _ _⟩
    · exact fun z hz => hwk z (by simp [hz])
  -- the second question, asked from the base dart
  have hcc₂ : Gc.RlinkConnected
      {z | Gc.Fband (([x0c, Gc.edge x0c] ++ Gc.walkq (Gc.node (Gc.edge x0c)) q₀)
        ++ Gc.walkq (Gc.node x0c) q₁) z ∧
        EdgeCentral Gc Gm (Gm.embedqz Gc x0c x0m qz) z} := by
    refine rlinkConnected_fband_walkq hpc hqc hP q₁ x0c _ ?_ ?_ ?_ hcc₁ ?_
    · exact fband_append.mpr (Or.inl ⟨x0c, by simp, Equiv.Perm.SameCycle.refl _ _⟩)
    · exact fband_append.mpr (Or.inl ⟨Gc.edge x0c, by simp, Equiv.Perm.SameCycle.refl _ _⟩)
    · intro z hz
      rcases List.mem_append.mp hz with hz' | hz'
      · exact haker z hz'
      · exact (hwk z (by simp [hz'])).1
    · intro z hz
      refine hwk z ?_
      simp only [List.cons_append, List.mem_cons, List.mem_append, hpc.edge_edge]
      exact Or.inr (Or.inr (Or.inr hz))
  refine rlinkConnected_congr ?_ hcc₂
  ext z
  simp only [Set.mem_ofPred_eq, and_congr_left_iff]
  intro _
  have hz := hqz.2.2.2 z
  rw [hsplitc, hpc.edge_edge] at hz
  rw [← hz]
  simp only [fband_append, fband_cons, fband_nil, or_false]
  tauto

/-- **A valid quiz that also fits the map gives a preembedding of the
configuration kernel into the map.**  This is the reference's
`quiz_preembedding`, the main result of the quiz development. -/
theorem quiz_preembedding (hpm : Gm.Plain) (hcm : Gm.Cubic) (hpc : Gc.Plain)
    (hqc : Gc.Quasicubic rc) (hqz : Gc.ValidQuiz rc x0c qz) (hfit : Gm.Fitqz x0m qz) :
    Preembedding Gc Gm (Gm.embedqz Gc x0c x0m qz) {z | Gc.Kernel rc z} where
  face := fun _ hz => embedqz_face hqz hfit hz
  arity := fun _ hz => embedqz_arity hqz hfit hz
  cover := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := (hqz.2.2.2 z).mpr hz
    exact ⟨w, hzw, embedqz_central hpm hcm hpc hqc hqz hfit hw⟩
  rlinked := embedqz_rlinked hpm hcm hpc hqc hqz hfit

end QuizEmbedding

end Hypermap

end FourColor

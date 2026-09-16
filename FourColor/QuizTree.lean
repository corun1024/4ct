import FourColor.Quiz

/-!
# Quiz trees: the configuration database, indexed by arity

The reducibility search has to test, at every node of the part it is
examining, whether any of the 633 reducible configurations occurs there.  A
`QuizTree` stores all their quizzes at once, indexed by the arities of the
three faces around the node the quiz starts at, so that a single lookup
retrieves the few quizzes that could possibly fit.

Because a quiz can be asked at any of the three darts of the node, and in
either orientation, the tree stores the rotations of each quiz as well — and
its reflection, unless the configuration is symmetric.  The large arities 9,
10 and 11 occur only at the hub of a configuration, so only the top node of
the tree branches on them; below it the branching is on the arities 5 to 8.

## Main definitions

* `QuizTree` — the tree, with `QuizTree.put`/`QuizTree.get1` to store and
  retrieve, and `QuizTree.storeQz` to store a quiz with its rotations.
* `Hypermap.Fit` — some quiz stored in the tree fits at some dart of a node.

## Main results

* `Hypermap.fit_put` — if a quiz stored by `put` makes the tree fit, then it
  fits somewhere in the map.
* `Hypermap.fit_storeQz`, `Hypermap.fit_storeCfQz` — the same for `storeQz`,
  which also accounts for reflections by passing to the mirror map.
-/

namespace FourColor

/-- A tree of quizzes, indexed by three arities.  `node` branches on the
arities 5 to 8, `hubNode` on "at most 8", 9, 10 and 11; `leaf` holds a triple
of residual questions, and the next triple stored under the same arities. -/
inductive QuizTree
  | nil
  | leaf (q₁ q₂ q₃ : Question) (t : QuizTree)
  | node (t₅ t₆ t₇ t₈ : QuizTree)
  | hubNode (t₅₈ t₉ t₁₀ t₁₁ : QuizTree)
  deriving DecidableEq, Repr

namespace QuizTree

/-- A tree that is not empty. -/
def Proper : QuizTree → Prop
  | nil => False
  | _ => True

instance (t : QuizTree) : Decidable t.Proper := by
  cases t <;> unfold Proper <;> infer_instance

/-! ### Storing -/

/-- Apply `qr` to the branch of `t` indexed by the arity `qa`.  A tree that
has no such branch is left alone. -/
def put1 (qa : QArity) (qr : QuizTree → QuizTree) : QuizTree → QuizTree
  | node t₅ t₆ t₇ t₈ =>
      match qa with
      | .qa5 => node (qr t₅) t₆ t₇ t₈
      | .qa6 => node t₅ (qr t₆) t₇ t₈
      | .qa7 => node t₅ t₆ (qr t₇) t₈
      | .qa8 => node t₅ t₆ t₇ (qr t₈)
      | _ => node t₅ t₆ t₇ t₈
  | hubNode t₅₈ t₉ t₁₀ t₁₁ =>
      match qa with
      | .qa9 => hubNode t₅₈ (qr t₉) t₁₀ t₁₁
      | .qa10 => hubNode t₅₈ t₉ (qr t₁₀) t₁₁
      | .qa11 => hubNode t₅₈ t₉ t₁₀ (qr t₁₁)
      | _ => hubNode (put1 qa qr t₅₈) t₉ t₁₀ t₁₁
  | t => t

/-- Store the triple `(q₁, q₂, q₃)` under the arities `qa₁, qa₂, qa₃`. -/
def put3 (qa₁ qa₂ qa₃ : QArity) (q₁ q₂ q₃ : Question) : QuizTree → QuizTree :=
  put1 qa₁ (put1 qa₂ (put1 qa₃ (leaf q₁ q₂ q₃)))

/-- Store the three rotations of a triple, at the three rotations of its
arities: the quiz may be met at any of the three darts of the node. -/
def put3rot (qa₁ qa₂ qa₃ : QArity) (q₁ q₂ q₃ : Question) (t : QuizTree) : QuizTree :=
  put3 qa₁ qa₂ qa₃ q₁ q₂ q₃ (put3 qa₂ qa₃ qa₁ q₂ q₃ q₁ (put3 qa₃ qa₁ qa₂ q₃ q₁ q₂ t))

/-- Store a triple with its rotations, unless the first arity is large — a
face with more than eight sides can only be the hub, so its quiz is met at one
dart only. -/
def put (qa₁ qa₂ qa₃ : QArity) (q₁ q₂ q₃ : Question) : QuizTree → QuizTree :=
  if 8 < qa₁.toNat then put3 qa₁ qa₂ qa₃ q₁ q₂ q₃ else put3rot qa₁ qa₂ qa₃ q₁ q₂ q₃

/-- The empty tree, with the branching structure already in place. -/
def empty : QuizTree :=
  let mkn t := node t t t t
  let n₂ := mkn (mkn nil)
  hubNode (mkn n₂) n₂ n₂ n₂

/-- Normalise a question so that its top node asks in both directions. -/
def normq : Question → Question
  | .ask1 qa => .askLR qa .ask0 .ask0
  | .askL qa ql => .askLR qa ql .ask0
  | .askR qa qr => .askLR qa .ask0 qr
  | q => q

/-- Store a quiz: its two questions are broken apart into the arities of the
three faces around the node the quiz starts at, and a residual triple.  Which
of the two questions supplies the third arity is decided so that the smaller
arity comes first. -/
def storeQz (qz : Quiz) : QuizTree → QuizTree :=
  match qz with
  | ⟨.askR qa₁ p₁, .askR qa₂ p₂⟩ =>
      match normq p₁, normq p₂ with
      | .askLR qa₁ᵣ p₁ₗ p₁ᵣ, .askLR qa₂ᵣ p₂ₗ p₂ᵣ =>
          if qa₁ᵣ.toNat < qa₂ᵣ.toNat then put qa₁ qa₂ qa₁ᵣ p₁ₗ p₂ p₁ᵣ
          else put qa₁ qa₂ᵣ qa₂ p₁ p₂ᵣ p₂ₗ
      | .askLR qa₁ᵣ p₁ₗ p₁ᵣ, _ => put qa₁ qa₂ qa₁ᵣ p₁ₗ p₂ p₁ᵣ
      | _, .askLR qa₂ᵣ p₂ₗ p₂ᵣ => put qa₁ qa₂ᵣ qa₂ p₁ p₂ᵣ p₂ₗ
      | _, _ => id
  | _ => id

/-- Store the quiz of a configuration, and its reflection unless the
configuration is symmetric. -/
def storeCfQz (qz : Quiz) (sym : Bool) (t : QuizTree) : QuizTree :=
  storeQz qz (if sym then t else storeQz qz.flip t)

/-- The number of triples the tree holds. -/
def size : QuizTree → ℕ
  | leaf _ _ _ t => size t + 1
  | node t₅ t₆ t₇ t₈ => size t₅ + (size t₆ + (size t₇ + size t₈))
  | hubNode t₅₈ t₉ t₁₀ t₁₁ => size t₅₈ + (size t₉ + (size t₁₀ + size t₁₁))
  | nil => 0

/-! ### Retrieving -/

/-- The branch of `t` indexed by the arity `qa`. -/
def get1 (qa : QArity) : QuizTree → QuizTree
  | node t₅ t₆ t₇ t₈ =>
      match qa with
      | .qa5 => t₅
      | .qa6 => t₆
      | .qa7 => t₇
      | .qa8 => t₈
      | _ => nil
  | hubNode t₅₈ t₉ t₁₀ t₁₁ =>
      match qa with
      | .qa9 => t₉
      | .qa10 => t₁₀
      | .qa11 => t₁₁
      | _ => get1 qa t₅₈
  | _ => nil

/-- The branch of `t` indexed by two arities. -/
def get2 (qa₂ qa₃ : QArity) (t : QuizTree) : QuizTree := get1 qa₃ (get1 qa₂ t)

/-- The branch of `t` indexed by three arities. -/
def get3 (qa₁ qa₂ qa₃ : QArity) (t : QuizTree) : QuizTree := get2 qa₂ qa₃ (get1 qa₁ t)

/-- Pop the top `hubNode`, so that the tree branches on small arities only. -/
def truncate : QuizTree → QuizTree
  | hubNode (node t₅ t₆ t₇ t₈) _ _ _ => node t₅ t₆ t₇ t₈
  | t => t

end QuizTree

/-! ### Fitting

A quiz triple stored in the tree fits at a node of a plain cubic hypermap when
the three faces around the node have the arities under which it is stored, and
the three residual questions fit at the three darts of the node.
-/

/-- The quiz that asks the three arities `qa₁, qa₂, qa₃` around a node, and
then the three residual questions. -/
def quiz3 (qa₁ qa₂ qa₃ : QArity) (q₁ q₂ q₃ : Question) : Quiz :=
  ⟨.askR qa₁ (.askLR qa₃ q₁ q₃), .askR qa₂ q₂⟩

namespace Hypermap

variable {D : Type*} (G : Hypermap D)

/-- A quiz fits at a dart exactly when its two questions fit at the two ends of
the dart's edge. -/
theorem fitqz_iff (x : D) (qz : Quiz) :
    G.Fitqz x qz ↔ G.Fitq x qz.fst ∧ G.Fitq (G.edge x) qz.snd := by
  rw [Fitqz, walkqz, Quiz.flat]
  exact G.fitq_append x qz.fst qz.snd.flat (G.walkq (G.edge x) qz.snd)

/-- A right question fits at a dart exactly when the arity is right and the
residual question fits after the right move. -/
theorem fitq_askR (x : D) (qa : QArity) (q : Question) :
    G.Fitq x (.askR qa q) ↔ qa.toNat = G.arity x ∧ G.Fitq (G.qstepR x) q := by
  simp [Fitq, Question.flat, walkq]

/-- A two-sided question fits at a dart exactly when the arity is right and the
two residual questions fit after the two moves. -/
theorem fitq_askLR (x : D) (qa : QArity) (p q : Question) :
    G.Fitq x (.askLR qa p q) ↔
      qa.toNat = G.arity x ∧ G.Fitq (G.qstepL x) p ∧ G.Fitq (G.qstepR x) q := by
  rw [Fitq]
  simp only [Question.flat, walkq, List.map_cons, List.cons.injEq]
  rw [and_congr_right_iff]
  intro _
  exact G.fitq_append _ p q.flat _

/-- The six tests a `quiz3` performs. -/
theorem fitqz_quiz3 (x : D) (qa₁ qa₂ qa₃ : QArity) (q₁ q₂ q₃ : Question) :
    G.Fitqz x (quiz3 qa₁ qa₂ qa₃ q₁ q₂ q₃) ↔
      (qa₁.toNat = G.arity x ∧ qa₃.toNat = G.arity (G.qstepR x) ∧
          G.Fitq (G.qstepL (G.qstepR x)) q₁ ∧ G.Fitq (G.qstepR (G.qstepR x)) q₃) ∧
        qa₂.toNat = G.arity (G.edge x) ∧ G.Fitq (G.qstepR (G.edge x)) q₂ := by
  rw [fitqz_iff]
  change G.Fitq x (.askR qa₁ (.askLR qa₃ q₁ q₃)) ∧ G.Fitq (G.edge x) (.askR qa₂ q₂) ↔ _
  rw [fitq_askR, fitq_askR, fitq_askLR]

/-! ### Lookup and storage -/

/-- The `QArity` recording the arity of the face of a dart. -/
noncomputable def qarity (x : D) : QArity := QArity.ofArity (G.arity x)

/-- The three faces around the node of `x` have arities a quiz tree can index,
that is, between 5 and 11. -/
def Fita (x : D) : Prop :=
  (G.qarity x).toNat = G.arity x ∧
    (G.qarity (G.node x)).toNat = G.arity (G.node x) ∧
      (G.qarity (G.node (G.node x))).toNat = G.arity (G.node (G.node x))

/-- Some triple in the list `t` fits at the three darts of the node of `x`. -/
def Fitl (x : D) : QuizTree → Prop
  | .leaf q₁ q₂ q₃ t =>
      (G.Fitq (G.qstepR x) q₁ ∧ G.Fitq (G.qstepR (G.node x)) q₂ ∧
          G.Fitq (G.qstepR (G.node (G.node x))) q₃) ∨ Fitl x t
  | _ => False

/-- Some quiz stored in the tree fits at some dart of the node of `x`. -/
def Fit (x : D) (t : QuizTree) : Prop :=
  G.Fita x ∧
    G.Fitl x (QuizTree.get3 (G.qarity x) (G.qarity (G.node x))
      (G.qarity (G.node (G.node x))) t)

section PlainCubic

variable {G}

/-- In a plain cubic hypermap the face of a dart is reached from it by two
node steps after an edge step. -/
theorem face_eq_node_node_edge (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.face y = G.node (G.node (G.edge y)) :=
  G.node.injective ((node_face G hp y).trans (hc.node_node_node (G.edge y)).symm)

/-- The right move at the far end of the face dart returns the edge. -/
theorem qstepR_edge_face (hp : G.Plain) (y : D) :
    G.qstepR (G.edge (G.face y)) = G.edge y := by
  rw [qstepR, hp.edge_edge, node_face G hp]

/-- The face dart has the arity of the first right move. -/
theorem arity_edge_face [Finite D] (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.arity (G.edge (G.face y)) = G.arity (G.qstepR y) := by
  rw [face_eq_node_node_edge hp hc, arity_edge_node]
  rfl

/-- The left move at the other end of the edge is the doubled right move. -/
theorem qstepL_edge (G : Hypermap D) (y : D) :
    G.qstepL (G.edge y) = G.qstepR (G.qstepR y) := rfl

/-- The right move at the face dart is the left move after a right move. -/
theorem qstepR_face (hp : G.Plain) (hc : G.Cubic) (y : D) :
    G.qstepR (G.face y) = G.qstepL (G.qstepR y) := by
  rw [qstepR, qstepL, face_eq_node_node_edge hp hc]
  rfl

/-- Rotating the triple of arities and questions moves the dart the quiz is
asked at to the next dart of the same node. -/
theorem fitqz_rot [Finite D] (hp : G.Plain) (hc : G.Cubic) (y : D)
    (qa₁ qa₂ qa₃ : QArity) (q₁ q₂ q₃ : Question) :
    G.Fitqz y (quiz3 qa₁ qa₂ qa₃ q₁ q₂ q₃) ↔
      G.Fitqz (G.edge (G.face y)) (quiz3 qa₃ qa₁ qa₂ q₃ q₁ q₂) := by
  simp only [fitqz_quiz3, hp.edge_edge, arity_face, qstepR_edge_face hp,
    arity_edge_face hp hc, qstepL_edge, qstepR_face hp hc]
  tauto

/-- Swapping the two questions of a quiz moves the dart it is asked at to the
other end of its edge. -/
theorem fitqz_swap [Finite D] (hp : G.Plain) (hc : G.Cubic) (y : D)
    (qa₁ qa₂ qa₃ : QArity) (q₁ q₂ q₃ : Question) :
    G.Fitqz y (quiz3 qa₁ qa₂ qa₃ q₁ q₂ q₃) ↔
      G.Fitqz (G.face y) ⟨.askR qa₁ q₁, .askR qa₃ (.askLR qa₂ q₃ q₂)⟩ := by
  rw [fitqz_quiz3, fitqz_iff]
  change _ ↔ G.Fitq (G.face y) (.askR qa₁ q₁) ∧
    G.Fitq (G.edge (G.face y)) (.askR qa₃ (.askLR qa₂ q₃ q₂))
  rw [fitq_askR, fitq_askR, fitq_askLR]
  simp only [arity_face, qstepR_face hp hc, arity_edge_face hp hc, qstepR_edge_face hp,
    qstepL_edge]
  tauto


/-- Storing under an arity either changes exactly that branch, or leaves the
branch we look up alone. -/
theorem get_put1 (qa qa' : QArity) (qr : QuizTree → QuizTree) (t : QuizTree) :
    (qa = qa' ∧ qr (QuizTree.get1 qa t) = QuizTree.get1 qa (QuizTree.put1 qa' qr t)) ∨
      QuizTree.get1 qa t = QuizTree.get1 qa (QuizTree.put1 qa' qr t) := by
  induction t with
  | nil => exact Or.inr rfl
  | leaf _ _ _ _ _ => exact Or.inr rfl
  | node t₅ t₆ t₇ t₈ _ _ _ _ =>
      cases qa' <;> cases qa <;> simp [QuizTree.put1, QuizTree.get1]
  | hubNode t₅₈ t₉ t₁₀ t₁₁ ih _ _ _ =>
      cases qa' <;> cases qa <;> simp [QuizTree.put1, QuizTree.get1] <;> tauto

/-- If the tree fits after a triple has been stored, then either that very
triple fits — at the dart across the edge of the second dart of the node — or
the tree already fitted. -/
theorem fit_put3 [Finite D] (hp : G.Plain) (hc : G.Cubic) (x : D) (qa₁ qa₂ qa₃ : QArity)
    (q₁ q₂ q₃ : Question) (t : QuizTree)
    (h : G.Fit x (QuizTree.put3 qa₁ qa₂ qa₃ q₁ q₂ q₃ t)) :
    G.Fitqz (G.edge (G.node x)) (quiz3 qa₁ qa₂ qa₃ q₁ q₂ q₃) ∨ G.Fit x t := by
  obtain ⟨hfita, hfitl⟩ := h
  rw [QuizTree.put3, QuizTree.get3, QuizTree.get2] at hfitl
  rcases get_put1 (G.qarity x) qa₁
      (QuizTree.put1 qa₂ (QuizTree.put1 qa₃ (QuizTree.leaf q₁ q₂ q₃))) t with ⟨e₁, hg₁⟩ | hg₁
  swap
  · exact Or.inr ⟨hfita, by rwa [QuizTree.get3, QuizTree.get2, hg₁]⟩
  rw [← hg₁] at hfitl
  rcases get_put1 (G.qarity (G.node x)) qa₂ (QuizTree.put1 qa₃ (QuizTree.leaf q₁ q₂ q₃))
      (QuizTree.get1 (G.qarity x) t) with ⟨e₂, hg₂⟩ | hg₂
  swap
  · exact Or.inr ⟨hfita, by rwa [QuizTree.get3, QuizTree.get2, hg₂]⟩
  rw [← hg₂] at hfitl
  rcases get_put1 (G.qarity (G.node (G.node x))) qa₃ (QuizTree.leaf q₁ q₂ q₃)
      (QuizTree.get1 (G.qarity (G.node x)) (QuizTree.get1 (G.qarity x) t))
    with ⟨e₃, hg₃⟩ | hg₃
  swap
  · exact Or.inr ⟨hfita, by rwa [QuizTree.get3, QuizTree.get2, hg₃]⟩
  rw [← hg₃] at hfitl
  rcases hfitl with ⟨f₁, f₂, f₃⟩ | hfitl
  swap
  · exact Or.inr ⟨hfita, by rwa [QuizTree.get3, QuizTree.get2]⟩
  -- the stored triple fits: assemble the quiz at the dart across the edge
  obtain ⟨ha₁, ha₂, ha₃⟩ := hfita
  subst e₁; subst e₂; subst e₃
  refine Or.inl ?_
  have hx₃ : G.qstepR (G.edge (G.node x)) = G.node (G.node x) := by
    rw [qstepR, hp.edge_edge]
  have hx₂ : G.edge (G.edge (G.node x)) = G.node x := hp.edge_edge _
  have hx₁ : G.qstepL (G.node (G.node x)) = G.qstepR x := by
    rw [qstepL, qstepR, hc.node_node_node]
  rw [fitqz_quiz3, hx₃, hx₂, hx₁]
  exact ⟨⟨by rw [ha₁, arity_edge_node], ha₃, f₁, f₃⟩, ha₂, f₂⟩

/-- If the tree fits after a triple has been stored with its rotations, then
that triple fits somewhere, or the tree already fitted. -/
theorem fit_put [Finite D] (hp : G.Plain) (hc : G.Cubic) (x : D) (qa₁ qa₂ qa₃ : QArity)
    (q₁ q₂ q₃ : Question) (t : QuizTree)
    (h : G.Fit x (QuizTree.put qa₁ qa₂ qa₃ q₁ q₂ q₃ t)) :
    (∃ y, G.Fitqz y (quiz3 qa₁ qa₂ qa₃ q₁ q₂ q₃)) ∨ G.Fit x t := by
  rw [QuizTree.put] at h
  split at h
  · rcases fit_put3 hp hc x _ _ _ _ _ _ _ h with h' | h'
    · exact Or.inl ⟨_, h'⟩
    · exact Or.inr h'
  rw [QuizTree.put3rot] at h
  rcases fit_put3 hp hc x _ _ _ _ _ _ _ h with h' | h'
  · exact Or.inl ⟨_, h'⟩
  rcases fit_put3 hp hc x _ _ _ _ _ _ _ h' with h'' | h''
  · exact Or.inl ⟨_, (fitqz_rot hp hc _ _ _ _ _ _ _).mp h''⟩
  rcases fit_put3 hp hc x _ _ _ _ _ _ _ h'' with h₃ | h₃
  · exact Or.inl ⟨_, (fitqz_rot hp hc _ _ _ _ _ _ _).mp
      ((fitqz_rot hp hc _ _ _ _ _ _ _).mp h₃)⟩
  · exact Or.inr h₃

/-- Normalising a question does not change where it fits. -/
theorem fitq_normq (G : Hypermap D) (x : D) (q : Question) :
    G.Fitq x (QuizTree.normq q) ↔ G.Fitq x q := by
  cases q <;> simp [QuizTree.normq, Fitq, Question.flat, walkq]

/-- Normalising the first question of a right quiz does not change where it
fits. -/
theorem fitqz_normq_fst (G : Hypermap D) (y : D) (qa₁ qa₂ : QArity) (p₁ p₂ : Question) :
    G.Fitqz y ⟨.askR qa₁ (QuizTree.normq p₁), .askR qa₂ p₂⟩ ↔
      G.Fitqz y ⟨.askR qa₁ p₁, .askR qa₂ p₂⟩ := by
  simp only [fitqz_iff, fitq_askR, fitq_normq]

/-- Normalising the second question of a right quiz does not change where it
fits. -/
theorem fitqz_normq_snd (G : Hypermap D) (y : D) (qa₁ qa₂ : QArity) (p₁ p₂ : Question) :
    G.Fitqz y ⟨.askR qa₁ p₁, .askR qa₂ (QuizTree.normq p₂)⟩ ↔
      G.Fitqz y ⟨.askR qa₁ p₁, .askR qa₂ p₂⟩ := by
  simp only [fitqz_iff, fitq_askR, fitq_normq]

/-- If the tree fits after a quiz has been stored, then that quiz is a right
quiz that fits somewhere, or the tree already fitted. -/
theorem fit_storeQz [Finite D] (hp : G.Plain) (hc : G.Cubic) (x : D) (qz : Quiz) (t : QuizTree)
    (h : G.Fit x (QuizTree.storeQz qz t)) :
    (qz.IsQuizR ∧ ∃ y, G.Fitqz y qz) ∨ G.Fit x t := by
  obtain ⟨f, s⟩ := qz
  cases f <;> cases s <;> first | exact Or.inr h | skip
  rename_i qa₁ p₁ qa₂ p₂
  -- the first question supplies the third arity
  have key₁ : ∀ (qa₁ᵣ : QArity) (p₁ₗ p₁ᵣ : Question),
      QuizTree.normq p₁ = .askLR qa₁ᵣ p₁ₗ p₁ᵣ →
      G.Fit x (QuizTree.put qa₁ qa₂ qa₁ᵣ p₁ₗ p₂ p₁ᵣ t) →
      ((Quiz.mk (.askR qa₁ p₁) (.askR qa₂ p₂)).IsQuizR ∧
        ∃ y, G.Fitqz y ⟨.askR qa₁ p₁, .askR qa₂ p₂⟩) ∨ G.Fit x t := by
    intro qa₁ᵣ p₁ₗ p₁ᵣ hq₁ hfit
    rcases fit_put hp hc x _ _ _ _ _ _ _ hfit with ⟨y, hy⟩ | hfit
    · refine Or.inl ⟨⟨trivial, trivial⟩, y, ?_⟩
      rw [← fitqz_normq_fst, hq₁]
      exact hy
    · exact Or.inr hfit
  -- the second question supplies the third arity
  have key₂ : ∀ (qa₂ᵣ : QArity) (p₂ₗ p₂ᵣ : Question),
      QuizTree.normq p₂ = .askLR qa₂ᵣ p₂ₗ p₂ᵣ →
      G.Fit x (QuizTree.put qa₁ qa₂ᵣ qa₂ p₁ p₂ᵣ p₂ₗ t) →
      ((Quiz.mk (.askR qa₁ p₁) (.askR qa₂ p₂)).IsQuizR ∧
        ∃ y, G.Fitqz y ⟨.askR qa₁ p₁, .askR qa₂ p₂⟩) ∨ G.Fit x t := by
    intro qa₂ᵣ p₂ₗ p₂ᵣ hq₂ hfit
    rcases fit_put hp hc x _ _ _ _ _ _ _ hfit with ⟨y, hy⟩ | hfit
    · refine Or.inl ⟨⟨trivial, trivial⟩, G.face y, ?_⟩
      rw [← fitqz_normq_snd, hq₂]
      exact (fitqz_swap hp hc y _ _ _ _ _ _).mp hy
    · exact Or.inr hfit
  cases hq₁ : QuizTree.normq p₁ <;> cases hq₂ : QuizTree.normq p₂ <;>
    simp only [QuizTree.storeQz, hq₁, hq₂, id_eq] at h <;>
    first
      | exact Or.inr h
      | exact key₁ _ _ _ hq₁ h
      | exact key₂ _ _ _ hq₂ h
      | (split at h
         · exact key₁ _ _ _ hq₁ h
         · exact key₂ _ _ _ hq₂ h)

/-- Reflecting a quiz does not change whether it is a right quiz. -/
theorem _root_.FourColor.Quiz.isQuizR_flip (qz : Quiz) : qz.flip.IsQuizR ↔ qz.IsQuizR := by
  obtain ⟨f, s⟩ := qz
  cases f <;> cases s <;> simp [Quiz.flip, Quiz.IsQuizR, Question.IsAskR]

/-- If the tree fits after a configuration's quiz has been stored, then that
quiz fits somewhere in the map or in its mirror, or the tree already fitted. -/
theorem fit_storeCfQz [Finite D] (hp : G.Plain) (hc : G.Cubic) (x : D) (qz : Quiz) (sym : Bool)
    (t : QuizTree) (h : G.Fit x (QuizTree.storeCfQz qz sym t)) :
    (qz.IsQuizR ∧ ((∃ y, G.Fitqz y qz) ∨ ∃ y, G.mirror.Fitqz y qz)) ∨ G.Fit x t := by
  rw [QuizTree.storeCfQz] at h
  rcases fit_storeQz hp hc x qz _ h with ⟨hqz, y, hy⟩ | h
  · exact Or.inl ⟨hqz, Or.inl ⟨y, hy⟩⟩
  cases sym with
  | true => exact Or.inr (by simpa using h)
  | false =>
      rcases fit_storeQz hp hc x qz.flip _ h with ⟨hqz, y, hy⟩ | h
      · have hqz' : qz.IsQuizR := (Quiz.isQuizR_flip qz).mp hqz
        exact Or.inl ⟨hqz', Or.inr ⟨G.face y, (fitqz_flip G hp hc hqz' y).mp hy⟩⟩
      · exact Or.inr h

end PlainCubic

/-! ### The empty tree -/

/-- Nothing is stored in the empty tree. -/
theorem not_fit_nil (x : D) : ¬ G.Fit x QuizTree.nil := by
  rintro ⟨-, h⟩
  exact h

/-- Looking up any three arities in the empty tree finds nothing. -/
theorem QuizTree.get3_empty (qa₁ qa₂ qa₃ : QArity) :
    QuizTree.get3 qa₁ qa₂ qa₃ QuizTree.empty = QuizTree.nil := by
  cases qa₁ <;> cases qa₂ <;> cases qa₃ <;> rfl

/-- The empty tree fits nowhere. -/
theorem not_fit_empty (x : D) : ¬ G.Fit x QuizTree.empty := by
  rintro ⟨-, h⟩
  rw [QuizTree.get3_empty] at h
  exact h

/-! ### Truncation -/

/-- Truncating only removes branches that were empty anyway. -/
theorem QuizTree.get1_truncate (qa : QArity) (t : QuizTree) :
    (QuizTree.get1 qa t.truncate).Proper → QuizTree.get1 qa t.truncate = QuizTree.get1 qa t := by
  cases t with
  | nil => intro h; exact absurd h (by simp [QuizTree.truncate, QuizTree.get1, QuizTree.Proper])
  | leaf _ _ _ _ => intro h; exact absurd h (by simp [QuizTree.truncate, QuizTree.get1,
      QuizTree.Proper])
  | node _ _ _ _ => intro _; rfl
  | hubNode t₅₈ _ _ _ =>
      cases t₅₈ <;> cases qa <;>
        simp_all [QuizTree.truncate, QuizTree.get1, QuizTree.Proper]

end Hypermap

end FourColor

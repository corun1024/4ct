import FourColor.Color

/-!
# Colouring trees

Sets of ring colouring traces are represented by a ternary tree indexed by edge
traces.  A tree is used either for a full set of unreachable traces or for a
subset that has just become reachable; in both cases all its leaves sit at the
same depth, the ring size minus one.  Trees for full unreachable sets record the
number of matching unreachable chromograms at their leaves, in unary, as a stack
of nested leaves.

## Main definitions

* `Ctree` — the tree type; `Ctree.Proper h t` is the well-formedness predicate.
* `Ctree.sub t et` — the multiplicity of the trace `et`; `Ctree.mem` its support.
* `Ctree.cons` — the node constructor that contracts empty nodes.
* `Ctree.union`, `Ctree.rotl`, `Ctree.rotr`, `Ctree.rotlr` — the set operations
  driving the reducibility iteration.
* `Ctree.disjoint` — the test used for checking contracts.

## References

Gonthier's `theories/proof/ctree.v`.
-/

namespace FourColor

open Color

/-- A trace colouring tree: a ternary tree indexed by edge traces.  Repeated
`leaf` constructors denote multiplicity. -/
inductive Ctree
  /-- A node with the subtrees for `c1`, `c2` and `c3`. -/
  | node (t₁ t₂ t₃ : Ctree)
  /-- A leaf; nesting records multiplicity. -/
  | leaf (t : Ctree)
  /-- The empty tree. -/
  | empty
  deriving DecidableEq, Repr, Inhabited

namespace Ctree

/-! ### Classifiers and accessors -/

def isEmpty : Ctree → Bool
  | .empty => true
  | _ => false

def isLeaf : Ctree → Bool
  | .leaf _ => true
  | _ => false

/-- A node all of whose subtrees are empty.  Empty nodes are always contracted,
so that emptiness can be tested by matching on `Ctree.empty`. -/
def isEmptyNode : Ctree → Bool
  | .node .empty .empty .empty => true
  | _ => false

/-- The immediate subtree indexed by a colour; empty unless `t` is a node and
the colour is nonzero. -/
def sel : Ctree → Color → Ctree
  | .node t₁ t₂ t₃, c => match c with
    | .c0 => .empty
    | .c1 => t₁
    | .c2 => t₂
    | .c3 => t₃
  | _, _ => .empty

/-- `Proper h t`: `t` has no empty nodes and no nodes under leaves, and all its
leaves are `h` nodes deep. -/
def Proper : ℕ → Ctree → Prop
  | _, .empty => True
  | h + 1, .node t₁ t₂ t₃ =>
      isEmptyNode (.node t₁ t₂ t₃) = false ∧ Proper h t₁ ∧ Proper h t₂ ∧ Proper h t₃
  | 0, .node _ _ _ => False
  | 0, .leaf lf => Proper 0 lf
  | _ + 1, .leaf _ => False

/-- The multiplicity of the trace `et` in `t`, viewed as a multiset. -/
def sub : Ctree → List Color → ℕ
  | .node t₁ t₂ t₃, e :: et => match e with
    | .c0 => 0
    | .c1 => sub t₁ et
    | .c2 => sub t₂ et
    | .c3 => sub t₃ et
  | .leaf lf, [] => sub lf [] + 1
  | _, _ => 0

/-- `et` occurs in `t`. -/
def mem (t : Ctree) (et : List Color) : Bool := sub t et != 0

/-- The canonical leaf of multiplicity `n`. -/
def leafOf : ℕ → Ctree
  | 0 => .empty
  | n + 1 => .leaf (leafOf n)

/-- The node constructor that contracts empty nodes. -/
def cons : Ctree → Ctree → Ctree → Ctree
  | .empty, .empty, .empty => .empty
  | t₁, t₂, t₃ => .node t₁ t₂ t₃

/-- The single-branch constructor: the node that is empty except for `t` at
colour `e`. -/
def consE : Color → Ctree → Ctree
  | .c0, _ => .empty
  | .c1, t => cons t .empty .empty
  | .c2, t => cons .empty t .empty
  | .c3, t => cons .empty .empty t

/-- Any proper leaf will do for reachable trees, so we share this one. -/
def simpleLeaf : Ctree := .leaf .empty

/-- The tree containing exactly the trace `et`, with multiplicity one. -/
def ofTrace (et : List Color) : Ctree := et.foldr consE simpleLeaf

/-- The union of two trace sets. -/
def union : Ctree → Ctree → Ctree
  | .node l₁ l₂ l₃, .node r₁ r₂ r₃ => cons (union l₁ r₁) (union l₂ r₂) (union l₃ r₃)
  | .empty, tr => tr
  | tl, .empty => tl
  | _, _ => simpleLeaf

/-- The image of a tree under the colour rotation `e231`. -/
def rotl : Ctree → Ctree
  | .node t₁ t₂ t₃ => cons (rotl t₃) (rotl t₁) (rotl t₂)
  | t => t

/-- The image of a tree under the colour rotation `e312`. -/
def rotr : Ctree → Ctree
  | .node t₁ t₂ t₃ => cons (rotr t₂) (rotr t₃) (rotr t₁)
  | t => t

/-- The initial reachable set: a tree together with both its rotations. -/
def consRot (t : Ctree) : Ctree := cons t (rotl t) (rotr t)

/-- An interlocked union of the two rotations, used in the inner loop. -/
def unionRotlr : Ctree → Ctree → Ctree
  | .node l₁ l₂ l₃, .node r₁ r₂ r₃ =>
      cons (unionRotlr l₃ r₂) (unionRotlr l₁ r₃) (unionRotlr l₂ r₁)
  | .leaf _, .leaf _ => simpleLeaf
  | tl, tr => union (rotl tl) (rotr tr)

/-- The union of both rotations of a tree. -/
def rotlr (t : Ctree) : Ctree := unionRotlr t t

/-- A disjointness test, used for checking contracts. -/
def disjoint : Ctree → Ctree → Bool
  | .leaf _, .leaf _ => false
  | .node l₁ l₂ l₃, .node r₁ r₂ r₃ =>
      disjoint l₁ r₁ && disjoint l₂ r₂ && disjoint l₃ r₃
  | _, _ => true

/-! ### Classifiers -/

theorem eq_empty_of_isEmpty {t : Ctree} (h : isEmpty t) : t = .empty := by
  cases t <;> simp [isEmpty] at h ⊢

theorem eq_node_of_isEmptyNode {t : Ctree} (h : isEmptyNode t) :
    t = .node .empty .empty .empty := by
  match t with
  | .node .empty .empty .empty => rfl
  | .node (.node _ _ _) _ _ | .node (.leaf _) _ _
  | .node _ (.node _ _ _) _ | .node _ (.leaf _) _
  | .node _ _ (.node _ _ _) | .node _ _ (.leaf _)
  | .leaf _ | .empty => simp [isEmptyNode] at h

@[simp] theorem sel_zero (t : Ctree) : sel t 0 = .empty := by cases t <;> rfl

@[simp] theorem sel_empty (e : Color) : sel .empty e = .empty := rfl

@[simp] theorem sel_node_c1 (t₁ t₂ t₃ : Ctree) : sel (.node t₁ t₂ t₃) c1 = t₁ := rfl

@[simp] theorem sel_node_c2 (t₁ t₂ t₃ : Ctree) : sel (.node t₁ t₂ t₃) c2 = t₂ := rfl

@[simp] theorem sel_node_c3 (t₁ t₂ t₃ : Ctree) : sel (.node t₁ t₂ t₃) c3 = t₃ := rfl

@[simp] theorem sel_leaf (t : Ctree) (e : Color) : sel (.leaf t) e = .empty := rfl

@[simp] theorem isLeaf_empty : isLeaf .empty = false := rfl

@[simp] theorem isLeaf_node (t₁ t₂ t₃ : Ctree) : isLeaf (.node t₁ t₂ t₃) = false := rfl

@[simp] theorem isLeaf_leaf (t : Ctree) : isLeaf (.leaf t) = true := rfl

theorem proper_sel {h : ℕ} {t : Ctree} (e : Color) (ht : Proper h t) :
    Proper (h - 1) (sel t e) := by
  match h, t with
  | _, .empty => cases e <;> trivial
  | 0, .leaf _ => cases e <;> trivial
  | h + 1, .node t₁ t₂ t₃ =>
    obtain ⟨_, h₁, h₂, h₃⟩ := ht
    cases e <;> simp only [sel] <;> first | trivial | assumption
  | 0, .node _ _ _ => exact absurd ht not_false
  | _ + 1, .leaf _ => exact absurd ht not_false

/-! ### Lookup -/

theorem sub_eq_zero_of_mem_zero : ∀ (t : Ctree) {et : List Color},
    (0 : Color) ∈ et → sub t et = 0 := by
  intro t
  induction t with
  | node t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    intro et h
    cases et with
    | nil => simp at h
    | cons e et =>
      rcases List.mem_cons.mp h with he | he
      · rw [← he]; rfl
      · cases e <;> simp only [sub] <;> first
          | rfl
          | exact ih₁ he | exact ih₂ he | exact ih₃ he
  | leaf lf _ =>
    intro et h
    cases et with
    | nil => simp at h
    | cons e et => rfl
  | empty => intro et _; cases et <;> rfl

theorem mem_eq_false_of_mem_zero (t : Ctree) {et : List Color} (h : (0 : Color) ∈ et) :
    mem t et = false := by simp [mem, sub_eq_zero_of_mem_zero t h]

@[simp] theorem mem_nil (t : Ctree) : mem t [] = isLeaf t := by
  cases t <;> simp [mem, sub, isLeaf]

@[simp] theorem sub_cons_eq_sub_sel (t : Ctree) (e : Color) (et : List Color) :
    sub t (e :: et) = sub (sel t e) et := by
  cases t <;> cases e <;> rfl

theorem mem_cons_eq_mem_sel (t : Ctree) (e : Color) (et : List Color) :
    mem t (e :: et) = mem (sel t e) et := by simp [mem]

theorem proper_leafOf (n : ℕ) : Proper 0 (leafOf n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ih

theorem sub_leafOf (n : ℕ) (et : List Color) :
    sub (leafOf n) et = if et = [] then n else 0 := by
  cases et with
  | nil =>
    simp only [if_pos rfl]
    induction n with
    | zero => rfl
    | succ n ih => simp [leafOf, sub, ih]
  | cons e et =>
    rw [ite_eq_right (List.cons_ne_nil e et)]
    cases n <;> rfl

/-! ### The contracting node constructor -/

theorem cons_spec (t₁ t₂ t₃ : Ctree) :
    cons t₁ t₂ t₃ = if isEmptyNode (.node t₁ t₂ t₃) then .empty else .node t₁ t₂ t₃ := by
  cases t₁ <;> cases t₂ <;> cases t₃ <;> rfl

@[simp] theorem isLeaf_cons (t₁ t₂ t₃ : Ctree) : isLeaf (cons t₁ t₂ t₃) = false := by
  cases t₁ <;> cases t₂ <;> cases t₃ <;> rfl

@[simp] theorem sel_cons (t₁ t₂ t₃ : Ctree) (e : Color) :
    sel (cons t₁ t₂ t₃) e = sel (.node t₁ t₂ t₃) e := by
  cases t₁ <;> cases t₂ <;> cases t₃ <;> cases e <;> rfl

@[simp] theorem sub_cons (t₁ t₂ t₃ : Ctree) (et : List Color) :
    sub (cons t₁ t₂ t₃) et = sub (.node t₁ t₂ t₃) et := by
  cases et with
  | nil => cases t₁ <;> cases t₂ <;> cases t₃ <;> rfl
  | cons e et => rw [sub_cons_eq_sub_sel, sub_cons_eq_sub_sel, sel_cons]

theorem mem_cons (t₁ t₂ t₃ : Ctree) (et : List Color) :
    mem (cons t₁ t₂ t₃) et = mem (.node t₁ t₂ t₃) et := by simp [mem]

theorem cons_proper {h : ℕ} {t₁ t₂ t₃ : Ctree} (h₁ : Proper h t₁) (h₂ : Proper h t₂)
    (h₃ : Proper h t₃) : Proper (h + 1) (cons t₁ t₂ t₃) := by
  rw [cons_spec]
  split
  · trivial
  · exact ⟨by simp_all, h₁, h₂, h₃⟩

@[simp] theorem sub_empty (et : List Color) : sub .empty et = 0 := by cases et <;> rfl

@[simp] theorem sub_leaf_cons (lf : Ctree) (e : Color) (et : List Color) :
    sub (.leaf lf) (e :: et) = 0 := rfl

@[simp] theorem sub_node_nil (t₁ t₂ t₃ : Ctree) : sub (.node t₁ t₂ t₃) [] = 0 := rfl

@[simp] theorem mem_empty (et : List Color) : mem .empty et = false := by
  cases et <;> simp [mem]

/-! ### The branch constructors -/

theorem sel_consE (e e' : Color) (t : Ctree) :
    sel (consE e t) e' = if e' = 0 then .empty else if e' = e then t else .empty := by
  cases e <;> cases e' <;> simp [consE]

theorem consE_proper {h : ℕ} (e : Color) {t : Ctree} (ht : Proper h t) :
    Proper (h + 1) (consE e t) := by
  cases e
  · trivial
  · exact cons_proper ht trivial trivial
  · exact cons_proper trivial ht trivial
  · exact cons_proper trivial trivial ht

@[simp] theorem ofTrace_nil : ofTrace [] = simpleLeaf := rfl

@[simp] theorem ofTrace_cons (e : Color) (et : List Color) :
    ofTrace (e :: et) = consE e (ofTrace et) := rfl

theorem ofTrace_proper {h : ℕ} {et : List Color} (hlen : et.length = h) :
    Proper h (ofTrace et) := by
  subst hlen
  induction et with
  | nil => trivial
  | cons e et ih => exact consE_proper e ih

/-- The tree of a trace contains that trace and nothing else. -/
theorem mem_ofTrace : ∀ (et : List Color), (0 : Color) ∉ et → ∀ (et' : List Color),
    (mem (ofTrace et) et' = true ↔ et' = et) := by
  intro et
  induction et with
  | nil =>
    intro _ et'
    cases et' with
    | nil => simp [simpleLeaf, mem, sub, isLeaf]
    | cons e et' => simp [simpleLeaf, mem, sub, sel]
  | cons e et ih =>
    intro h et'
    have he : e ≠ 0 := fun hz => h (by simp [hz])
    have het : (0 : Color) ∉ et := fun hz => h (List.mem_cons_of_mem _ hz)
    cases et' with
    | nil =>
      simp only [ofTrace_cons, mem_nil, Bool.false_eq_true, false_iff]
      constructor
      · cases e <;> simp [consE]
      · exact fun hc => absurd hc (by simp)
    | cons e' et'' =>
      rw [ofTrace_cons, mem_cons_eq_mem_sel, sel_consE]
      by_cases h0 : e' = 0
      · rw [ite_eq_left h0]
        simp only [mem_empty, Bool.false_eq_true, false_iff]
        intro hc
        exact he (by rw [← (List.cons.inj hc).1, h0])
      · rw [ite_eq_right h0]
        by_cases hee : e' = e
        · rw [ite_eq_left hee, ih het et'']
          simp [hee]
        · rw [ite_eq_right hee]
          simp only [mem_empty, Bool.false_eq_true, false_iff]
          exact fun hc => hee (List.cons.inj hc).1

/-! ### Union -/

@[simp] theorem union_empty_left (t : Ctree) : union .empty t = t := by cases t <;> rfl

@[simp] theorem union_empty_right (t : Ctree) : union t .empty = t := by cases t <;> rfl

theorem union_comm : ∀ (t₁ t₂ : Ctree), union t₁ t₂ = union t₂ t₁ := by
  intro t₁
  induction t₁ with
  | node a b c iha ihb ihc =>
    intro t₂; cases t₂ with
    | node a' b' c' => simp only [union, iha, ihb, ihc]
    | leaf _ => rfl
    | empty => rfl
  | leaf l ih => intro t₂; cases t₂ <;> rfl
  | empty => intro t₂; cases t₂ <;> rfl

theorem union_proper : ∀ (h : ℕ) (tl tr : Ctree), Proper h tl → Proper h tr →
    Proper h (union tl tr) := by
  intro h
  induction h with
  | zero =>
    intro tl tr htl htr
    match tl, tr with
    | .empty, _ => simpa using htr
    | .leaf _, .empty => simpa using htl
    | .leaf _, .leaf _ => trivial
    | .leaf _, .node _ _ _ => exact absurd htr not_false
    | .node _ _ _, _ => exact absurd htl not_false
  | succ h ih =>
    intro tl tr htl htr
    match tl, tr with
    | .empty, _ => simpa using htr
    | _, .empty => simpa using htl
    | .node a b c, .node a' b' c' =>
      obtain ⟨_, ha, hb, hc⟩ := htl
      obtain ⟨_, ha', hb', hc'⟩ := htr
      exact cons_proper (ih _ _ ha ha') (ih _ _ hb hb') (ih _ _ hc hc')
    | .leaf _, _ => exact absurd htl not_false
    | .node _ _ _, .leaf _ => exact absurd htr not_false

theorem mem_union : ∀ (h : ℕ) (tl tr : Ctree) (et : List Color),
    Proper h tl → Proper h tr → mem (union tl tr) et = (mem tl et || mem tr et) := by
  intro h
  induction h with
  | zero =>
    intro tl tr et htl htr
    match tl, tr with
    | .empty, _ => simp
    | .leaf _, .empty => simp
    | .leaf _, .leaf _ => cases et <;> simp [union, simpleLeaf, mem, sub]
    | .leaf _, .node _ _ _ => exact absurd htr not_false
    | .node _ _ _, _ => exact absurd htl not_false
  | succ h ih =>
    intro tl tr et htl htr
    match tl, tr with
    | .empty, _ => simp
    | _, .empty => simp
    | .node a b c, .node a' b' c' =>
      obtain ⟨_, ha, hb, hc⟩ := htl
      obtain ⟨_, ha', hb', hc'⟩ := htr
      rw [union, mem_cons]
      cases et with
      | nil => simp [mem, sub]
      | cons e et =>
        cases e <;> simp only [mem_cons_eq_mem_sel, sel] <;> first
          | simp
          | exact ih _ _ et ha ha' | exact ih _ _ et hb hb' | exact ih _ _ et hc hc'
    | .leaf _, _ => exact absurd htl not_false
    | .node _ _ _, .leaf _ => exact absurd htr not_false

/-! ### Rotations -/

theorem sub_rotl : ∀ (et : List Color) (t : Ctree),
    sub (rotl t) et = sub t (et.map EdgePerm.e312) := by
  intro et
  induction et with
  | nil => intro t; cases t <;> simp [rotl, sub]
  | cons e et ih =>
    intro t
    cases t with
    | node t₁ t₂ t₃ => cases e <;> simp [rotl, EdgePerm.apply, ih]
    | leaf l => cases e <;> simp [rotl, sub]
    | empty => cases e <;> simp [rotl, sub]

theorem sub_rotr : ∀ (et : List Color) (t : Ctree),
    sub (rotr t) et = sub t (et.map EdgePerm.e231) := by
  intro et
  induction et with
  | nil => intro t; cases t <;> simp [rotr, sub]
  | cons e et ih =>
    intro t
    cases t with
    | node t₁ t₂ t₃ => cases e <;> simp [rotr, EdgePerm.apply, ih]
    | leaf l => cases e <;> simp [rotr, sub]
    | empty => cases e <;> simp [rotr, sub]

theorem mem_rotl (t : Ctree) (et : List Color) :
    mem (rotl t) et = mem t (et.map EdgePerm.e312) := by simp [mem, sub_rotl]

theorem mem_rotr (t : Ctree) (et : List Color) :
    mem (rotr t) et = mem t (et.map EdgePerm.e231) := by simp [mem, sub_rotr]

theorem rotl_proper : ∀ (h : ℕ) (t : Ctree), Proper h t → Proper h (rotl t) := by
  intro h
  induction h with
  | zero =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact ht
    | .node _ _ _ => exact absurd ht not_false
  | succ h ih =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact absurd ht not_false
    | .node t₁ t₂ t₃ =>
      obtain ⟨_, h₁, h₂, h₃⟩ := ht
      exact cons_proper (ih _ h₃) (ih _ h₁) (ih _ h₂)

theorem rotr_proper : ∀ (h : ℕ) (t : Ctree), Proper h t → Proper h (rotr t) := by
  intro h
  induction h with
  | zero =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact ht
    | .node _ _ _ => exact absurd ht not_false
  | succ h ih =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact absurd ht not_false
    | .node t₁ t₂ t₃ =>
      obtain ⟨_, h₁, h₂, h₃⟩ := ht
      exact cons_proper (ih _ h₂) (ih _ h₃) (ih _ h₁)

theorem consRot_proper {h : ℕ} {t : Ctree} (ht : Proper h t) :
    Proper (h + 1) (consRot t) :=
  cons_proper ht (rotl_proper h t ht) (rotr_proper h t ht)

/-- The initial reachable set contains exactly the normalised tails. -/
theorem mem_consRot (t : Ctree) (et : List Color) :
    mem (consRot t) et = mem t (normTail et) := by
  cases et with
  | nil =>
    rw [consRot, mem_nil, isLeaf_cons, normTail]
    exact (mem_eq_false_of_mem_zero t (by simp)).symm
  | cons e et =>
    rw [consRot, mem_cons, mem_cons_eq_mem_sel, normTail]
    cases e
    · rw [ite_eq_left (show Color.c0 = 0 from rfl)]
      simp only [Color.c0_eq_zero, sel_zero, mem_empty]
      exact (mem_eq_false_of_mem_zero t (by simp)).symm
    · rw [ite_eq_right (by simp), sel_node_c1]
      simp [EdgePerm.rotTo]
    · rw [ite_eq_right (by simp), sel_node_c2, mem_rotl]
      simp [EdgePerm.rotTo]
    · rw [ite_eq_right (by simp), sel_node_c3, mem_rotr]
      simp [EdgePerm.rotTo]

/-! ### Union of rotations -/

theorem union_cons (a b c d e f : Ctree) :
    union (cons a b c) (cons d e f) = cons (union a d) (union b e) (union c f) := by
  by_cases h1 : a = .empty ∧ b = .empty ∧ c = .empty
  · obtain ⟨rfl, rfl, rfl⟩ := h1
    simp [cons]
  · by_cases h2 : d = .empty ∧ e = .empty ∧ f = .empty
    · obtain ⟨rfl, rfl, rfl⟩ := h2
      simp [cons]
    · have hc1 : cons a b c = .node a b c := by
        cases a <;> cases b <;> cases c <;> simp_all [cons]
      have hc2 : cons d e f = .node d e f := by
        cases d <;> cases e <;> cases f <;> simp_all [cons]
      rw [hc1, hc2, union]

theorem unionRotlr_eq : ∀ (t u : Ctree), unionRotlr t u = union (rotl t) (rotr u) := by
  intro t
  induction t with
  | node t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    intro u
    cases u with
    | node u₁ u₂ u₃ =>
      rw [unionRotlr, ih₁, ih₂, ih₃, rotl, rotr, union_cons]
    | leaf _ => rfl
    | empty => rfl
  | leaf l ih => intro u; cases u <;> rfl
  | empty => intro u; cases u <;> rfl

theorem rotlr_spec (t : Ctree) : rotlr t = union (rotl t) (rotr t) := unionRotlr_eq t t

theorem rotlr_proper {h : ℕ} {t : Ctree} (ht : Proper h t) : Proper h (rotlr t) := by
  rw [rotlr_spec]
  exact union_proper h _ _ (rotl_proper h t ht) (rotr_proper h t ht)

theorem mem_rotlr {h : ℕ} {t : Ctree} (et : List Color) (ht : Proper h t) :
    mem (rotlr t) et = (mem t (et.map EdgePerm.e312) || mem t (et.map EdgePerm.e231)) := by
  rw [rotlr_spec, mem_union h _ _ et (rotl_proper h t ht) (rotr_proper h t ht),
    mem_rotl, mem_rotr]

/-! ### Disjointness -/

theorem disjoint_eq_false_iff : ∀ (tl tr : Ctree),
    disjoint tl tr = false ↔ ∃ et, mem tl et = true ∧ mem tr et = true := by
  intro tl
  induction tl with
  | node l₁ l₂ l₃ ih₁ ih₂ ih₃ =>
    intro tr
    cases tr with
    | node r₁ r₂ r₃ =>
      rw [disjoint]
      constructor
      · intro h
        simp only [Bool.and_eq_false_iff] at h
        rcases h with (h | h) | h
        · obtain ⟨et, hl, hr⟩ := (ih₁ r₁).mp h
          exact ⟨Color.c1 :: et, by simpa [mem_cons_eq_mem_sel] using hl,
            by simpa [mem_cons_eq_mem_sel] using hr⟩
        · obtain ⟨et, hl, hr⟩ := (ih₂ r₂).mp h
          exact ⟨Color.c2 :: et, by simpa [mem_cons_eq_mem_sel] using hl,
            by simpa [mem_cons_eq_mem_sel] using hr⟩
        · obtain ⟨et, hl, hr⟩ := (ih₃ r₃).mp h
          exact ⟨Color.c3 :: et, by simpa [mem_cons_eq_mem_sel] using hl,
            by simpa [mem_cons_eq_mem_sel] using hr⟩
      · rintro ⟨et, hl, hr⟩
        cases et with
        | nil => simp at hl
        | cons e et =>
          rw [mem_cons_eq_mem_sel] at hl hr
          cases e
          · simp at hl
          · simp only [sel_node_c1] at hl hr
            simp [(ih₁ r₁).mpr ⟨et, hl, hr⟩]
          · simp only [sel_node_c2] at hl hr
            simp [(ih₂ r₂).mpr ⟨et, hl, hr⟩]
          · simp only [sel_node_c3] at hl hr
            simp [(ih₃ r₃).mpr ⟨et, hl, hr⟩]
    | leaf _ =>
      simp only [disjoint, Bool.true_eq_false, false_iff]
      rintro ⟨et, hl, hr⟩
      cases et with
      | nil => simp at hl
      | cons e et => rw [mem_cons_eq_mem_sel] at hr; simp at hr
    | empty => simp [disjoint]
  | leaf l ih =>
    intro tr
    cases tr with
    | node r₁ r₂ r₃ =>
      simp only [disjoint, Bool.true_eq_false, false_iff]
      rintro ⟨et, hl, hr⟩
      cases et with
      | nil => simp at hr
      | cons e et => rw [mem_cons_eq_mem_sel] at hl; simp at hl
    | leaf _ => exact ⟨fun _ => ⟨[], by simp, by simp⟩, fun _ => rfl⟩
    | empty => simp [disjoint]
  | empty => intro tr; cases tr <;> simp [disjoint]

/-- The direction of the disjointness test the development actually uses. -/
theorem mem_eq_false_of_disjoint {tl tr : Ctree} {et : List Color}
    (hd : disjoint tl tr = true) (hr : mem tr et = true) : mem tl et = false := by
  by_contra hl
  simp only [Bool.not_eq_false] at hl
  have := (disjoint_eq_false_iff tl tr).mpr ⟨et, hl, hr⟩
  rw [hd] at this
  exact Bool.noConfusion this

end Ctree

end FourColor

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate

/-!
# List primitives used by the Four Colour Theorem development

The reference development (Gonthier's Coq proof) is built on the MathComp `seq`
library.  Most of that library has a `Mathlib` counterpart, but two workhorse
operations do not: `pairmap`, which maps a binary function along consecutive
pairs of a list, and MathComp's `scanl`, which differs from `List.scanl` in that
it omits the seed value from the output.  Both are needed to define edge traces
in `FourColor.Color`, so we introduce them here together with the cancellation
lemmas that make them mutually inverse.

## Main definitions

* `FourColor.pairmap f x l` — `[f x y₁, f y₁ y₂, …, f yₙ₋₁ yₙ]` for `l = [y₁, …, yₙ]`.
* `FourColor.scanl g x l` — `[g x y₁, g (g x y₁) y₂, …]`, MathComp's `scanl`.
-/

namespace FourColor

variable {α β : Type*}

/-- `pairmap f x [y₁, …, yₙ]` is `[f x y₁, f y₁ y₂, …, f yₙ₋₁ yₙ]`: the function
`f` applied to each consecutive pair of `x :: l`.  This is MathComp's `pairmap`. -/
def pairmap (f : α → α → β) : α → List α → List β
  | _, [] => []
  | x, y :: l => f x y :: pairmap f y l

/-- `scanl g x [y₁, …, yₙ]` is `[g x y₁, g (g x y₁) y₂, …]`.  This is MathComp's
`scanl`, which unlike `List.scanl` does not emit the seed `x`. -/
def scanl (g : α → β → α) : α → List β → List α
  | _, [] => []
  | x, y :: l => g x y :: scanl g (g x y) l

@[simp] theorem pairmap_nil (f : α → α → β) (x : α) : pairmap f x [] = [] := rfl

@[simp] theorem pairmap_cons (f : α → α → β) (x y : α) (l : List α) :
    pairmap f x (y :: l) = f x y :: pairmap f y l := rfl

@[simp] theorem scanl_nil (g : α → β → α) (x : α) : scanl g x [] = [] := rfl

@[simp] theorem scanl_cons (g : α → β → α) (x : α) (y : β) (l : List β) :
    scanl g x (y :: l) = g x y :: scanl g (g x y) l := rfl

@[simp] theorem length_pairmap (f : α → α → β) (x : α) (l : List α) :
    (pairmap f x l).length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => simp [ih]

@[simp] theorem length_scanl (g : α → β → α) (x : α) (l : List β) :
    (scanl g x l).length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => simp [ih]

/-- `scanl g x` undoes `pairmap f x` when `g x` cancels `f x`. -/
theorem pairmapK {f : α → α → β} {g : α → β → α} (h : ∀ x y, g x (f x y) = y) (x : α)
    (l : List α) : scanl g x (pairmap f x l) = l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => simp [h, ih]

/-- `pairmap f x` undoes `scanl g x` when `f x` cancels `g x`. -/
theorem scanlK {f : α → α → β} {g : α → β → α} (h : ∀ x y, f x (g x y) = y) (x : α)
    (l : List β) : pairmap f x (scanl g x l) = l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => simp [h, ih]

/-- `Mathlib`'s `List.scanl` emits the seed; MathComp's does not.  This is the
bridge between the two. -/
theorem list_scanl_eq (g : α → β → α) (x : α) (l : List β) :
    List.scanl g x l = x :: scanl g x l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => rw [List.scanl_cons, ih]; rfl

theorem pairmap_append_singleton (f : α → α → β) (x y : α) (l : List α) :
    pairmap f x (l ++ [y]) = pairmap f x l ++ [f (l.getLastD x) y] := by
  induction l generalizing x with
  | nil => rfl
  | cons z l ih => rw [List.getLastD_cons]; simpa using ih z

theorem getD_pairmap {α β : Type*} (f : α → α → β) (x : α) (l : List α) (d : α) (db : β) :
    ∀ i, i < l.length → (pairmap f x l).getD i db = f ((x :: l).getD i d) (l.getD i d) := by
  induction l generalizing x with
  | nil => intro i hi; simp at hi
  | cons y l ih =>
    intro i hi
    match i with
    | 0 => rfl
    | i + 1 =>
      simp only [pairmap_cons, List.getD_cons_succ]
      exact ih y i (by simpa using hi)

end FourColor

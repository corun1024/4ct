import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation

/-!
# Duplicate-free paths

Cutting the loops out of a path leaves a duplicate-free path with the same
endpoints, made of darts of the original.  This is the reference's `shortenP`,
and it is what turns a connectivity argument into a Moebius path or a ring.

Endpoints are taken with `List.getLastD`, which carries no nonemptiness proof
and so rewrites freely.

## Main results

* `List.IsChain.exists_nodup` — every chain contains a duplicate-free chain
  with the same endpoints.
-/

namespace FourColor

variable {α : Type*} {r : α → α → Prop}

/-- The last dart of a nonempty list does not depend on the default. -/
theorem getLastD_cons (x y : α) (p : List α) : (y :: p).getLastD x = p.getLastD y := by
  match p with
  | [] => rfl
  | c :: p => rfl

theorem getLastD_mem_cons (x : α) (p : List α) : p.getLastD x ∈ x :: p := by
  match p with
  | [] => simp
  | y :: p => exact List.mem_cons_of_mem _ (List.getLast_mem _)

theorem getLastD_map {β : Type*} (f : α → β) (p : List α) (a : α) :
    (p.map f).getLastD (f a) = f (p.getLastD a) := by
  match p with
  | [] => rfl
  | y :: p =>
    show ((y :: p).map f).getLast (by simp) = f ((y :: p).getLast (by simp))
    rw [List.getLast_map]

theorem getLastD_append_cons (x a : α) (p q : List α) :
    (p ++ a :: q).getLastD x = q.getLastD a := by
  induction p generalizing x with
  | nil => exact getLastD_cons x a q
  | cons b p ih => rw [List.cons_append, getLastD_cons, ih]

theorem getLast?_cons_eq_some (x : α) : ∀ (q : List α),
    (x :: q).getLast? = some (q.getLastD x)
  | [] => rfl
  | c :: q => by
    rw [List.getLast?_cons_cons, getLast?_cons_eq_some c q, getLastD_cons]

/-- Joining two chains by a link from the last dart of the first to the first
dart of the second. -/
theorem isChain_append_cons : ∀ {l₁ : List α} {x y : α} {l₂ : List α},
    List.IsChain r (x :: l₁) → r (l₁.getLastD x) y → List.IsChain r (y :: l₂) →
      List.IsChain r ((x :: l₁) ++ y :: l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro x y l₂ _ hstep h₂; exact List.IsChain.cons_cons hstep h₂
  | cons c l₁ ih =>
    intro x y l₂ h₁ hstep h₂
    obtain ⟨hxc, htail⟩ := List.isChain_cons_cons.mp h₁
    rw [List.cons_append]
    refine List.IsChain.cons_cons hxc ?_
    exact ih htail (by rwa [getLastD_cons] at hstep) h₂

/-- Cutting out the loops of a chain leaves a duplicate-free chain with the
same endpoints, whose darts are darts of the original. -/
theorem List.IsChain.exists_nodup {x : α} : ∀ {p : List α}, List.IsChain r (x :: p) →
    ∃ q : List α, List.IsChain r (x :: q) ∧ (x :: q).Nodup ∧
      q.getLastD x = p.getLastD x ∧ ∀ w ∈ q, w ∈ p := by
  intro p
  induction p generalizing x with
  | nil => exact fun _ => ⟨[], List.IsChain.singleton x, by simp, rfl, by simp⟩
  | cons a p ih =>
    intro hp
    obtain ⟨hxa, hchain⟩ := List.isChain_cons_cons.mp hp
    obtain ⟨q, hq, hnodup, hlast, hsub⟩ := ih hchain
    by_cases hx : x ∈ a :: q
    · -- the path returns to `x`: drop everything before the return
      obtain ⟨q₁, q₂, hsplit⟩ := List.append_of_mem hx
      have hq' : List.IsChain r (q₁ ++ x :: q₂) := hsplit ▸ hq
      have hnodup' : (q₁ ++ x :: q₂).Nodup := hsplit ▸ hnodup
      refine ⟨q₂, (List.isChain_append.mp hq').2.1, (List.nodup_append.mp hnodup').2.1, ?_, ?_⟩
      · rw [getLastD_cons x a p, ← hlast, ← getLastD_append_cons x x q₁ q₂, ← hsplit,
          getLastD_cons]
      · intro w hw
        have hwq : w ∈ a :: q := by rw [hsplit]; simp [hw]
        rcases List.mem_cons.mp hwq with rfl | hwq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hwq)
    · refine ⟨a :: q, List.IsChain.cons_cons hxa hq,
        List.nodup_cons.mpr ⟨hx, hnodup⟩, ?_, ?_⟩
      · rw [getLastD_cons, getLastD_cons, hlast]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hw)

end FourColor

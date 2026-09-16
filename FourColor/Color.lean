import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.DeriveFintype
import FourColor.Seq

/-!
# The four colours and edge traces

The four colours form the Klein four-group: colour addition is bitwise `xor` on
the two-bit representation, and this is the operation the whole development is
built on, since edge traces are sums of adjacent face colours.  We therefore
give `Color` an `AddCommGroup` instance outright, which lets `Mathlib`'s algebra
API (`List.sum`, `add_comm`, …) do the work that the reference development does
by hand.

The permutations of the three nonzero colours act on `Color` by additive
automorphisms; `EdgePerm` is this group, presented concretely so that it
computes, with `EdgePerm.eIJK` denoting the permutation sending `c1 ↦ cI`,
`c2 ↦ cJ`, `c3 ↦ cK`.

## Main definitions

* `Color` — the four colours, an `AddCommGroup`.
* `EdgePerm` — the six permutations fixing `Color.c0`, a `Group` acting on `Color`.
* `trace`, `partialTrace`, `completeTrace`, `untrace` — edge traces of a colouring.
* `evenNormTail` — the normalised even tail of a trace, the canonical form used
  by the reducibility check.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/color.v` of the Coq development.
-/

namespace FourColor

/-- The four colours.  `c0` is the zero of the Klein four-group structure. -/
inductive Color
  | c0 | c1 | c2 | c3
  deriving DecidableEq, Repr, Inhabited

namespace Color

instance : Fintype Color :=
  ⟨⟨{c0, c1, c2, c3}, by decide⟩, fun c => by cases c <;> decide⟩

/-- Colour addition: bitwise `xor` of the two-bit representations. -/
protected def add : Color → Color → Color
  | c0, c => c
  | c, c0 => c
  | c1, c1 => c0 | c1, c2 => c3 | c1, c3 => c2
  | c2, c1 => c3 | c2, c2 => c0 | c2, c3 => c1
  | c3, c1 => c2 | c3, c2 => c1 | c3, c3 => c0

instance : AddCommGroup Color where
  add := Color.add
  zero := c0
  neg := id
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add_cancel := by decide
  add_comm := by decide
  nsmul := @nsmulRec Color ⟨c0⟩ ⟨Color.add⟩
  zsmul := @zsmulRec Color ⟨c0⟩ ⟨Color.add⟩ ⟨id⟩ (@nsmulRec Color ⟨c0⟩ ⟨Color.add⟩)
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl
  sub_eq_add_neg := fun _ _ => rfl

/-- The zero of the group structure is `c0`; we normalise towards `0`. -/
@[simp] theorem c0_eq_zero : c0 = 0 := rfl

/-- Every colour is its own additive inverse. -/
@[simp] theorem neg_eq (c : Color) : -c = c := rfl

/-- Colour addition is an involution in each argument: the group is elementary
abelian of exponent 2. -/
@[simp] theorem add_self (c : Color) : c + c = 0 := by cases c <;> rfl

theorem add_eq_zero_iff : ∀ {c d : Color}, c + d = 0 ↔ c = d := by decide

/-- The low bit of a colour: set for `c1` and `c3`. -/
def lo : Color → Bool
  | c0 | c2 => false
  | c1 | c3 => true

/-- The high bit of a colour: set for `c2` and `c3`. -/
def hi : Color → Bool
  | c0 | c1 => false
  | c2 | c3 => true

@[simp] theorem lo_zero : (0 : Color).lo = false := rfl
@[simp] theorem lo_c1 : c1.lo = true := rfl
@[simp] theorem lo_c2 : c2.lo = false := rfl
@[simp] theorem lo_c3 : c3.lo = true := rfl
@[simp] theorem hi_zero : (0 : Color).hi = false := rfl
@[simp] theorem hi_c1 : c1.hi = false := rfl
@[simp] theorem hi_c2 : c2.hi = true := rfl
@[simp] theorem hi_c3 : c3.hi = true := rfl

/-- The colour with the given high and low bits. -/
def ofBits : Bool → Bool → Color
  | false, false => c0
  | false, true  => c1
  | true,  false => c2
  | true,  true  => c3

/-- Colours are exactly pairs of bits. -/
def bitsEquiv : Color ≃ Bool × Bool where
  toFun c := (c.hi, c.lo)
  invFun p := ofBits p.1 p.2
  left_inv := by intro c; cases c <;> rfl
  right_inv := by intro p; obtain ⟨b₁, b₀⟩ := p; cases b₁ <;> cases b₀ <;> rfl

@[simp] theorem hi_add : ∀ c d : Color, (c + d).hi = (c.hi ^^ d.hi) := by decide
@[simp] theorem lo_add : ∀ c d : Color, (c + d).lo = (c.lo ^^ d.lo) := by decide

end Color

open Color

/-- The six permutations of the three nonzero colours.  `eIJK` sends `c1 ↦ cI`,
`c2 ↦ cJ` and `c3 ↦ cK`, and fixes `c0`. -/
inductive EdgePerm
  | e123 | e132 | e213 | e231 | e312 | e321
  deriving DecidableEq, Repr, Inhabited

namespace EdgePerm

instance : Fintype EdgePerm :=
  ⟨⟨{e123, e132, e213, e231, e312, e321}, by decide⟩, fun g => by cases g <;> decide⟩

/-- The action of an edge permutation on colours. -/
def apply : EdgePerm → Color → Color
  | _,    c0 => c0
  | e123, c => c
  | e132, c1 => c1 | e132, c2 => c3 | e132, c3 => c2
  | e213, c1 => c2 | e213, c2 => c1 | e213, c3 => c3
  | e231, c1 => c2 | e231, c2 => c3 | e231, c3 => c1
  | e312, c1 => c3 | e312, c2 => c1 | e312, c3 => c2
  | e321, c1 => c3 | e321, c2 => c2 | e321, c3 => c1

instance : CoeFun EdgePerm (fun _ => Color → Color) := ⟨apply⟩

/-- The rotation that a colour induces on the other two: the reference's
`edge_rot`, used to normalise a trace at an edge. -/
def edgeRot : Color → EdgePerm
  | c0 => e123
  | c1 => e123
  | c2 => e312
  | c3 => e231

/-- The edge permutation acting as `f`, when `f` is one; junk otherwise.  Since
an edge permutation is determined by the images of `c1` and `c2`, this is a
lookup on those two values. -/
def ofFun (f : Color → Color) : EdgePerm :=
  match f c1, f c2 with
  | .c1, .c3 => e132
  | .c2, .c1 => e213
  | .c2, .c3 => e231
  | .c3, .c1 => e312
  | .c3, .c2 => e321
  | _, _ => e123

instance : Group EdgePerm where
  mul g h := ofFun (fun c => g (h c))
  one := e123
  inv := fun g => match g with | e231 => e312 | e312 => e231 | g => g
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

@[simp] theorem e123_eq_one : e123 = 1 := rfl

@[simp] theorem one_apply (c : Color) : (1 : EdgePerm) c = c := by cases c <;> rfl

@[simp] theorem mul_apply : ∀ (g h : EdgePerm) (c : Color), (g * h) c = g (h c) := by decide

@[simp] theorem apply_zero (g : EdgePerm) : g 0 = 0 := by cases g <;> rfl

@[simp] theorem apply_add : ∀ (g : EdgePerm) (c d : Color), g (c + d) = g c + g d := by decide

@[simp] theorem apply_eq_zero : ∀ {g : EdgePerm} {c : Color}, g c = 0 ↔ c = 0 := by decide

theorem apply_injective (g : EdgePerm) : Function.Injective g := by
  have h : ∀ (g : EdgePerm) (c d : Color), g c = g d → c = d := by decide
  exact fun {c d} => h g c d

@[simp] theorem inv_apply_apply : ∀ (g : EdgePerm) (c : Color), g⁻¹ (g c) = c := by decide

@[simp] theorem apply_inv_apply : ∀ (g : EdgePerm) (c : Color), g (g⁻¹ c) = c := by decide

/-- Edge permutations are additive automorphisms of `Color`. -/
def toAddEquiv (g : EdgePerm) : Color ≃+ Color where
  toFun := g
  invFun := fun c => g⁻¹ c
  left_inv := inv_apply_apply g
  right_inv := apply_inv_apply g
  map_add' := apply_add g

@[simp] theorem coe_toAddEquiv (g : EdgePerm) : ⇑(toAddEquiv g) = g := rfl

/-- Every injective colour map fixing `c0` is an edge permutation. -/
theorem apply_ofFun_of_injective {f : Color → Color} (hf : Function.Injective f)
    (h0 : f 0 = 0) (c : Color) : ofFun f c = f c := by
  have h : ∀ f : Color → Color, (∀ a b, f a = f b → a = b) → f 0 = 0 →
      ∀ c, ofFun f c = f c := by
    set_option maxRecDepth 10000 in decide +kernel
  exact h f (fun _ _ hab => hf hab) h0 c

/-- The rotation taking a nonzero colour to `c1`; junk (the identity) on `c0`. -/
def rotTo : Color → EdgePerm
  | c0 | c1 => e123
  | c2 => e312
  | c3 => e231

@[simp] theorem rotTo_apply_self {c : Color} (hc : c ≠ 0) : rotTo c c = c1 := by
  cases c <;> simp_all [rotTo, apply]

/-- The nonzero colours are `c`, `rotTo c⁻¹ c1`-style rotations of it: for `c ≠ 0`
the four colours are exactly `0`, `c`, `e312 c`, `e231 c`. -/
theorem eq_of_ne_zero : ∀ {c d : Color}, c ≠ 0 →
    d = 0 ∨ d = c ∨ d = e312 c ∨ d = e231 c := by decide

end EdgePerm

end FourColor

namespace FourColor

open Color EdgePerm

/-! ### Edge traces

A colouring of the faces around a configuration gives rise to a *trace*: the
list of sums of adjacent colours.  The trace of a cyclic colouring sums to zero,
so its last entry is redundant; `partialTrace` drops it and `completeTrace`
restores it.  Normalising a trace by the rotation taking its head to `c1`, and
then by the transposition of `c2` and `c3` if needed, gives the canonical form
`evenNormTail` on which the reducibility check operates.
-/

/-- The partial (linear) trace of a colouring: the sums of adjacent colours. -/
def partialTrace : List Color → List Color
  | [] => []
  | c :: l => pairmap (· + ·) c l

/-- Complete a partial trace by appending the redundant closing colour. -/
def completeTrace (et : List Color) : List Color := et ++ [et.sum]

/-- The (cyclic) trace of a colouring. -/
def trace : List Color → List Color
  | [] => []
  | c :: l => completeTrace (partialTrace (c :: l))

/-- The right-rotated trace of a colouring. -/
def rotTrace (l : List Color) : List Color := pairmap (· + ·) (l.getLastD 0) l

/-- Recover a colouring from its trace, given the colour it starts at. -/
def untrace (c₀ : Color) : List Color → List Color
  | [] => []
  | et@(_ :: _) => List.scanl (· + ·) c₀ et.dropLast

/-- A trace is *proper* when it does not begin with `c0`.  Traces of proper
colourings never contain `c0` at all, so `[c0]` serves as a failure value. -/
def ProperTrace (et : List Color) : Prop := et.headD 0 ≠ 0

instance (et : List Color) : Decidable (ProperTrace et) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- The normalised tail of a trace: rotate so the head becomes `c1`, then drop
it.  Improper traces are sent to the failure value `[c0]`. -/
def normTail : List Color → List Color
  | [] => [0]
  | c :: et => if c = 0 then [0] else et.map (rotTo c)

/-- A list of colours is *even* when `c2` occurs before `c3` in it, if at all. -/
def evenTail : List Color → Bool :=
  List.foldr (fun c b => match c with | .c2 => true | .c3 => false | _ => b) true

/-- A trace is even when its normalised tail is. -/
def evenTrace (et : List Color) : Bool := evenTail (normTail et)

/-- The transposition of `c2` and `c3` needed to make a trace even. -/
def evenPerm (et : List Color) : EdgePerm := if evenTrace et then 1 else e132

/-- An even representative of a trace, up to swapping `c2` and `c3`. -/
def evenize (et : List Color) : List Color := et.map (evenPerm et)

/-- The canonical form of a trace: its normalised, even tail. -/
def evenNormTail (et : List Color) : List Color := (normTail et).map (evenPerm et)

/-- The canonical form of the partial trace of a colouring. -/
def evenPartialTail (l : List Color) : List Color := evenNormTail (partialTrace l)

/-- The number of colours with the high bit set, used to validate the initial
colouring tree. -/
def countHi (l : List Color) : ℕ := l.countP (·.hi)

/-! #### Sums and permutations -/

theorem map_sum (g : EdgePerm) (l : List Color) : (l.map g).sum = g l.sum :=
  (map_list_sum (g.toAddEquiv.toAddMonoidHom) l).symm

theorem hi_sum_eq_false {l : List Color} (h : ∀ c ∈ l, c.hi = false) : l.sum.hi = false := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.sum_cons, hi_add, h c (by simp), ih fun x hx => h x (by simp [hx])]
    rfl

@[simp] theorem sum_completeTrace (et : List Color) : (completeTrace et).sum = 0 := by
  simp [completeTrace]

@[simp] theorem length_completeTrace (et : List Color) :
    (completeTrace et).length = et.length + 1 := by simp [completeTrace]

theorem mem_zero_completeTrace {et : List Color} :
    (0 : Color) ∈ completeTrace et ↔ et.sum = 0 ∨ (0 : Color) ∈ et := by
  simp [completeTrace, or_comm, eq_comm]

theorem properTrace_completeTrace {et : List Color} :
    ProperTrace (completeTrace et) ↔ ProperTrace et := by
  cases et <;> simp [ProperTrace, completeTrace]

theorem map_completeTrace (g : EdgePerm) (et : List Color) :
    completeTrace (et.map g) = (completeTrace et).map g := by
  simp [completeTrace, map_sum]

theorem completeTrace_injective : Function.Injective completeTrace := by
  intro s t h
  have hlen : s.length = t.length := by
    have := congrArg List.length h; simpa [completeTrace] using this
  exact (List.append_inj h hlen).1

/-! #### Properness and normalisation -/

@[simp] theorem properTrace_map {g : EdgePerm} {et : List Color} :
    ProperTrace (et.map g) ↔ ProperTrace et := by
  cases et with
  | nil => simp [ProperTrace]
  | cons c et => simp [ProperTrace, not_congr (apply_eq_zero (g := g) (c := c))]

@[simp] theorem mem_zero_map {g : EdgePerm} {et : List Color} :
    (0 : Color) ∈ et.map g ↔ (0 : Color) ∈ et := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨c, hc, h⟩; rwa [apply_eq_zero.mp h] at hc
  · exact fun h => ⟨0, h, by simp⟩

theorem mem_zero_normTail {et : List Color} :
    (0 : Color) ∈ normTail et ↔ ¬ ProperTrace et ∨ (0 : Color) ∈ et := by
  cases et with
  | nil => simp [normTail, ProperTrace]
  | cons c et =>
    by_cases hc : c = 0
    · simp [normTail, ProperTrace, hc]
    · have hc' : ¬ (0 : Color) = c := fun h => hc h.symm
      simp [normTail, ProperTrace, hc, hc']

/-! #### Evenness -/

/-- One step of the `evenTail` scan: `c2` forces evenness, `c3` forces oddness,
and the other two colours carry the accumulated value through. -/
def evenStep (c : Color) (b : Bool) : Bool :=
  match c with | .c2 => true | .c3 => false | _ => b

theorem evenTail_eq_foldr (l : List Color) : evenTail l = List.foldr evenStep true l := rfl

theorem foldr_evenStep_const {l : List Color} (h : ∀ c ∈ l, c.hi = false) (b : Bool) :
    List.foldr evenStep b l = b := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc := h c (by simp)
    have : evenStep c (List.foldr evenStep b l) = List.foldr evenStep b l := by
      cases c <;> simp_all [evenStep, Color.hi]
    rw [List.foldr_cons, this, ih fun x hx => h x (by simp [hx])]

theorem foldr_evenStep_indep {l : List Color} (h : ∃ c ∈ l, c.hi = true) (b b' : Bool) :
    List.foldr evenStep b l = List.foldr evenStep b' l := by
  induction l with
  | nil => simp at h
  | cons c l ih =>
    rcases h with ⟨x, hx, hx'⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · cases x <;> simp_all [evenStep, Color.hi]
    · by_cases hc : c.hi = true
      · cases c <;> simp_all [evenStep, Color.hi]
      · simp only [List.foldr_cons, ih ⟨x, hx, hx'⟩]
  
theorem evenTail_concat {u : List Color} {v : Color}
    (hv : (∀ c ∈ u, c.hi = false) → v.hi = false) :
    evenTail (u ++ [v]) = evenTail u := by
  by_cases h : ∀ c ∈ u, c.hi = false
  · have hv' := hv h
    rw [evenTail_eq_foldr, evenTail_eq_foldr, List.foldr_append,
      foldr_evenStep_const h, foldr_evenStep_const h]
    cases v <;> simp_all [evenStep, Color.hi]
  · push Not at h
    obtain ⟨c, hc, hc'⟩ := h
    have hex : ∃ c ∈ u, c.hi = true := ⟨c, hc, by simpa using hc'⟩
    rw [evenTail_eq_foldr, evenTail_eq_foldr, List.foldr_append]
    exact foldr_evenStep_indep hex _ _

/-- Completing a trace does not change its parity. -/
theorem evenTrace_completeTrace (et : List Color) :
    evenTrace (completeTrace et) = evenTrace et := by
  cases et with
  | nil => rfl
  | cons e t =>
    by_cases he : e = 0
    · simp [evenTrace, normTail, completeTrace, he]
    have hcons : completeTrace (e :: t) = e :: (t ++ [(e :: t).sum]) := by
      simp [completeTrace]
    rw [evenTrace, evenTrace, hcons, normTail, normTail, ite_eq_right he, ite_eq_right he,
      List.map_append, List.map_cons, List.map_nil]
    refine evenTail_concat ?_
    intro h
    have hsum : ((t.map (rotTo e)).sum).hi = false := hi_sum_eq_false h
    have : (rotTo e) ((e :: t).sum) = (rotTo e) e + (t.map (rotTo e)).sum := by
      rw [List.sum_cons, apply_add, map_sum]
    rw [this, hi_add, rotTo_apply_self he, hsum]
    rfl

end FourColor

namespace FourColor

open Color EdgePerm

/-! #### The trace as a cyclic pairwise sum

The recursive definition of `trace` is the one the reducibility computation
runs, but every equational property is clearer through the closed form
`trace l = zipWith (+) l (l.rotate 1)`: the trace pairs each colour with its
cyclic successor.  Rotation and reversal laws then follow from `Mathlib`'s list
API instead of bespoke inductions.
-/

theorem sum_pairmap (c : Color) (l : List Color) :
    (pairmap (· + ·) c l).sum = c + l.getLastD c := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih =>
    rw [pairmap_cons, List.sum_cons, ih, List.getLastD_cons, ← add_assoc, add_assoc c x x,
      add_self, add_zero]

theorem zipWith_reverse {α β γ : Type*} (f : α → β → γ) (a : List α) (b : List β)
    (h : a.length = b.length) :
    List.zipWith f a.reverse b.reverse = (List.zipWith f a b).reverse := by
  induction a using List.reverseRecOn generalizing b with
  | nil => cases b <;> simp_all
  | append_singleton a' x ih =>
    induction b using List.reverseRecOn with
    | nil => simp at h
    | append_singleton b' y _ =>
      have h' : a'.length = b'.length := by simpa using h
      rw [List.reverse_append, List.reverse_append, List.zipWith_append (by simp),
        List.zipWith_append h', List.reverse_append, ih b' h']
      simp

theorem zipWith_rotate_one {α β γ : Type*} (f : α → β → γ) (a : List α) (b : List β)
    (h : a.length = b.length) :
    List.zipWith f (a.rotate 1) (b.rotate 1) = (List.zipWith f a b).rotate 1 := by
  cases a with
  | nil => cases b <;> simp_all
  | cons x t₁ =>
    cases b with
    | nil => simp at h
    | cons y t₂ =>
      have h' : t₁.length = t₂.length := by simpa using h
      simp [List.rotate_cons_succ, List.zipWith_append h']

theorem zipWith_rotate {α β γ : Type*} (f : α → β → γ) (a : List α) (b : List β) (n : ℕ)
    (h : a.length = b.length) :
    List.zipWith f (a.rotate n) (b.rotate n) = (List.zipWith f a b).rotate n := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    have h₁ : (a.rotate 1).length = (b.rotate 1).length := by simpa using h
    calc List.zipWith f (a.rotate (n + 1)) (b.rotate (n + 1))
        = List.zipWith f ((a.rotate 1).rotate n) ((b.rotate 1).rotate n) := by
          rw [List.rotate_rotate, List.rotate_rotate, Nat.add_comm]
      _ = (List.zipWith f (a.rotate 1) (b.rotate 1)).rotate n := ih _ _ h₁
      _ = ((List.zipWith f a b).rotate 1).rotate n := by rw [zipWith_rotate_one f a b h]
      _ = (List.zipWith f a b).rotate (n + 1) := by rw [List.rotate_rotate, Nat.add_comm]

theorem zipWith_cons_append (c d : Color) (l : List Color) :
    List.zipWith (· + ·) (c :: l) (l ++ [d]) = pairmap (· + ·) c l ++ [l.getLastD c + d] := by
  induction l generalizing c with
  | nil => simp
  | cons x t ih =>
    rw [List.getLastD_cons, List.cons_append, List.zipWith_cons_cons, ih x, pairmap_cons,
      List.cons_append]

/-- The trace pairs each colour of a colouring with its cyclic successor. -/
theorem trace_eq_zipWith (l : List Color) :
    trace l = List.zipWith (· + ·) l (l.rotate 1) := by
  cases l with
  | nil => rfl
  | cons c l =>
    rw [trace, partialTrace, completeTrace, sum_pairmap, List.rotate_cons_succ,
      List.rotate_zero, zipWith_cons_append, add_comm]

@[simp] theorem length_trace (l : List Color) : (trace l).length = l.length := by
  simp [trace_eq_zipWith]

@[simp] theorem sum_trace (l : List Color) : (trace l).sum = 0 := by
  cases l with
  | nil => rfl
  | cons c l => exact sum_completeTrace _

/-- Rotating a colouring rotates its trace. -/
theorem trace_rotate (n : ℕ) (l : List Color) : trace (l.rotate n) = (trace l).rotate n := by
  rw [trace_eq_zipWith, trace_eq_zipWith, ← zipWith_rotate _ _ _ _ (by simp),
    List.rotate_rotate, List.rotate_rotate, Nat.add_comm]

/-- Moving the first colour of a colouring to the back rotates its trace; this is
the reference development's `trace_rcons`. -/
theorem trace_append_singleton (c : Color) (l : List Color) :
    trace (l ++ [c]) = (trace (c :: l)).rotate 1 := by
  rw [← trace_rotate, List.rotate_cons_succ, List.rotate_zero]

theorem trace_cons (c : Color) (l : List Color) :
    trace (c :: l) = pairmap (· + ·) c (l ++ [c]) := by
  rw [trace, partialTrace, completeTrace, sum_pairmap, pairmap_append_singleton, add_comm]

theorem trace_map (g : EdgePerm) (l : List Color) :
    trace (l.map g) = (trace l).map g := by
  simp only [trace_eq_zipWith, ← List.map_rotate, List.map_zipWith, List.zipWith_map, apply_add]

/-- Shifting every colour of a colouring by a constant leaves the trace unchanged. -/
theorem trace_map_add (c : Color) (l : List Color) :
    trace (l.map (c + ·)) = trace l := by
  simp only [trace_eq_zipWith, ← List.map_rotate, List.zipWith_map]
  refine congrArg (fun f => List.zipWith f l (l.rotate 1)) ?_
  funext x y
  rw [add_add_add_comm, add_self, zero_add]

/-- Reversing a colouring reverses and rotates its trace. -/
private theorem rotate_one_add_sub {α : Type*} (m : List α) :
    m.rotate (1 + (m.length - 1 % m.length)) = m := by
  rcases m with _ | ⟨a, t⟩
  · simp
  · rcases Nat.lt_or_ge (a :: t).length 2 with h1 | h2
    · have hlen : (a :: t).length = 1 := by simp only [List.length_cons] at h1 ⊢; omega
      have hmod : 1 % (a :: t).length = 0 := by rw [hlen]
      have hr := List.rotate_length_mul (a :: t) 2
      rw [hlen] at hr
      rw [hmod, Nat.sub_zero, hlen]
      simpa using hr
    · have hmod : 1 % (a :: t).length = 1 := Nat.mod_eq_of_lt (by omega)
      have harith : 1 + ((a :: t).length - 1) = (a :: t).length := by omega
      rw [hmod, harith, List.rotate_length]

theorem trace_reverse (l : List Color) :
    trace l.reverse = ((trace l).reverse).rotate 1 := by
  have hlen : l.length = (l.rotate 1).length := by simp
  rw [trace_eq_zipWith, trace_eq_zipWith, List.rotate_reverse l 1,
    List.rotate_reverse (List.zipWith (· + ·) l (l.rotate 1)) 1,
    zipWith_reverse _ l (l.rotate (l.length - 1 % l.length)) (by simp)]
  refine congrArg List.reverse ?_
  rw [List.length_zipWith, List.length_rotate, Nat.min_self,
    ← zipWith_rotate _ _ _ (l.length - 1 % l.length) hlen, List.rotate_rotate,
    rotate_one_add_sub l]
  exact (List.zipWith_comm_of_comm add_comm).symm

end FourColor

namespace FourColor

open Color EdgePerm

/-! #### The right-rotated trace

`rotTrace` pairs each colour with its cyclic *predecessor*; it is the form in
which traces arise when walking a configuration's perimeter backwards, and is
used by the Kempe-chain and configuration-colouring layers.
-/

theorem rotTrace_rotate_one (l : List Color) : rotTrace (l.rotate 1) = trace l := by
  cases l with
  | nil => rfl
  | cons c t =>
    rw [List.rotate_cons_succ, List.rotate_zero, rotTrace, List.getLastD_concat, trace_cons]

theorem rotTrace_rotate (l : List Color) : rotTrace (l.rotate 1) = (rotTrace l).rotate 1 := by
  cases l with
  | nil => rfl
  | cons c t =>
    rw [List.rotate_cons_succ, List.rotate_zero, rotTrace, rotTrace, List.getLastD_concat,
      List.getLastD_cons, pairmap_cons, List.rotate_cons_succ, List.rotate_zero,
      pairmap_append_singleton]

theorem trace_eq_rotTrace (l : List Color) : trace l = (rotTrace l).rotate 1 := by
  rw [← rotTrace_rotate_one, rotTrace_rotate]

/-! #### Recovering a colouring from its trace -/

theorem add_add_cancel (x y : Color) : x + (x + y) = y := by
  rw [← add_assoc, add_self, zero_add]

theorem untrace_of_ne_nil (c₀ : Color) {et : List Color} (h : et ≠ []) :
    untrace c₀ et = c₀ :: scanl (· + ·) c₀ et.dropLast := by
  cases et with
  | nil => exact absurd rfl h
  | cons _ _ => exact list_scanl_eq _ _ _

theorem untrace_trace (c₀ : Color) (l : List Color) :
    untrace c₀ (trace (c₀ :: l)) = c₀ :: l := by
  have hne : trace (c₀ :: l) ≠ [] := by
    intro h; simpa using congrArg List.length h
  rw [untrace_of_ne_nil _ hne, trace, partialTrace, completeTrace, List.dropLast_concat,
    pairmapK add_add_cancel]

theorem trace_untrace (c₀ : Color) {et : List Color} (h : et.sum = 0) :
    trace (untrace c₀ et) = et := by
  rcases eq_or_ne et [] with rfl | hne
  · rfl
  · rw [untrace_of_ne_nil c₀ hne, trace, partialTrace, scanlK add_add_cancel, completeTrace]
    have hlast : et.dropLast ++ [et.getLast hne] = et := List.dropLast_append_getLast hne
    have hsum : et.dropLast.sum + et.getLast hne = 0 := by
      have hcat : (et.dropLast ++ [et.getLast hne]).sum = et.sum := by rw [hlast]
      simpa using hcat.trans h
    rw [show et.dropLast.sum = et.getLast hne from add_eq_zero_iff.mp hsum, hlast]

/-! #### Partial traces -/

theorem pairmap_map_add (c x : Color) (l : List Color) :
    pairmap (· + ·) (c + x) (l.map (c + ·)) = pairmap (· + ·) x l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih =>
    rw [List.map_cons, pairmap_cons, pairmap_cons, ih, add_add_add_comm, add_self, zero_add]

theorem partialTrace_map_add (c : Color) (l : List Color) :
    partialTrace (l.map (c + ·)) = partialTrace l := by
  cases l with
  | nil => rfl
  | cons x l => exact pairmap_map_add c x l

theorem pairmap_map (g : EdgePerm) (x : Color) (l : List Color) :
    pairmap (· + ·) (g x) (l.map g) = (pairmap (· + ·) x l).map g := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => rw [List.map_cons, pairmap_cons, pairmap_cons, List.map_cons, ih, apply_add]

theorem partialTrace_map (g : EdgePerm) (l : List Color) :
    partialTrace (l.map g) = (partialTrace l).map g := by
  cases l with
  | nil => rfl
  | cons x l => exact pairmap_map g x l

/-! #### Normalisation invariants -/

@[simp] theorem map_one_edgePerm (l : List Color) : l.map (1 : EdgePerm) = l := by
  rw [show ((1 : EdgePerm) : Color → Color) = id from funext one_apply, List.map_id]

@[simp] theorem map_map_edgePerm (g h : EdgePerm) (l : List Color) :
    (l.map h).map g = l.map (g * h) := by
  rw [List.map_map]
  exact congrArg (fun f => l.map f) (funext fun c => (mul_apply g h c).symm)

@[simp] theorem evenTail_nil : evenTail [] = true := rfl

@[simp] theorem evenTail_cons (c : Color) (u : List Color) :
    evenTail (c :: u) = evenStep c (evenTail u) := rfl

theorem evenPerm_eq_one_or (et : List Color) : evenPerm et = 1 ∨ evenPerm et = e132 := by
  unfold evenPerm; split <;> simp

theorem evenTail_map_e132 {u : List Color} (h : evenTail u = false) :
    evenTail (u.map e132) = true := by
  induction u with
  | nil => simp at h
  | cons c u ih => cases c <;> simp_all [evenStep, EdgePerm.apply]

theorem map_e132_eq_self {u : List Color} (h₁ : evenTail u = true)
    (h₂ : evenTail (u.map e132) = true) : u.map e132 = u := by
  induction u with
  | nil => simp
  | cons c u ih => cases c <;> simp_all [evenStep, EdgePerm.apply]

/-- The canonical form of a trace is even. -/
theorem evenTail_evenNormTail (et : List Color) : evenTail (evenNormTail et) = true := by
  rw [evenNormTail, evenPerm]
  split
  · rename_i h; rw [map_one_edgePerm]; exact h
  · rename_i h
    exact evenTail_map_e132 (Bool.eq_false_iff.mpr h)

theorem rotTo_mul {g : EdgePerm} (hg : g = 1 ∨ g = e132) {c : Color} (hc : c ≠ 0) :
    rotTo (g c) * g = g * rotTo c := by
  have key : ∀ c : Color, c ≠ 0 → rotTo (e132 c) * e132 = e132 * rotTo c := by decide
  rcases hg with rfl | rfl
  · simp
  · exact key c hc

theorem normTail_evenize (et : List Color) : normTail (evenize et) = evenNormTail et := by
  cases et with
  | nil => simp [evenize, normTail, evenNormTail]
  | cons c t =>
    by_cases hc : c = 0
    · subst hc; simp [evenize, normTail, evenNormTail]
    · have hgc : ¬ (evenPerm (c :: t) c = 0) := by simpa using hc
      simp only [evenize, List.map_cons, normTail, evenNormTail, ite_eq_right hgc, ite_eq_right hc,
        map_map_edgePerm]
      rw [rotTo_mul (evenPerm_eq_one_or (c :: t)) hc]

theorem evenTrace_evenize (et : List Color) : evenTrace (evenize et) = true := by
  rw [evenTrace, normTail_evenize]; exact evenTail_evenNormTail et

/-- A proper trace is, up to an edge permutation, `c1` followed by its canonical
form. -/
theorem exists_map_eq_cons_evenNormTail {et : List Color} (h : ProperTrace et) :
    ∃ g : EdgePerm, et.map g = c1 :: evenNormTail et := by
  have hp : ProperTrace (evenize et) := properTrace_map.mpr h
  cases hu : evenize et with
  | nil => rw [hu] at hp; exact absurd rfl hp
  | cons e rest =>
    have he : e ≠ 0 := by have := hp; rw [hu] at this; exact this
    refine ⟨rotTo e * evenPerm et, ?_⟩
    rw [← map_map_edgePerm, ← evenize, hu, List.map_cons, rotTo_apply_self he,
      ← normTail_evenize, hu, normTail, ite_eq_right he]

/-- The canonical form of a trace is invariant under edge permutations. -/
theorem evenNormTail_map (g : EdgePerm) (et : List Color) :
    evenNormTail (et.map g) = evenNormTail et := by
  by_cases h : ProperTrace et
  · have hg : ProperTrace (et.map g) := properTrace_map.mpr h
    obtain ⟨k, hk⟩ := exists_map_eq_cons_evenNormTail h
    obtain ⟨k', hk'⟩ := exists_map_eq_cons_evenNormTail hg
    rw [map_map_edgePerm] at hk'
    set m := k' * g * k⁻¹ with hmdef
    have hmul : (et.map k).map m = et.map (k' * g) := by
      rw [map_map_edgePerm, hmdef, inv_mul_cancel_right]
    rw [hk, List.map_cons, hk'] at hmul
    obtain ⟨hc1, hlist⟩ := List.cons.inj hmul
    have hmcase : m = 1 ∨ m = e132 := by
      have key : ∀ m : EdgePerm, m c1 = c1 → m = 1 ∨ m = e132 := by decide
      exact key m hc1
    rcases hmcase with hm1 | hm1
    · rw [← hlist, hm1, map_one_edgePerm]
    · rw [← hlist, hm1]
      refine map_e132_eq_self (evenTail_evenNormTail et) ?_
      rw [← hm1, hlist]
      exact evenTail_evenNormTail _
  · have hg : ¬ ProperTrace (et.map g) := fun hc => h (properTrace_map.mp hc)
    have himp : ∀ {u : List Color}, ¬ ProperTrace u → evenNormTail u = [0] := by
      intro u hu
      cases u with
      | nil => simp [evenNormTail, normTail]
      | cons c t =>
        have hc : c = 0 := by
          by_contra hne
          exact hu hne
        simp [evenNormTail, normTail, hc]
    rw [himp hg, himp h]

/-- The canonical form of a partial trace is invariant under any injective
recolouring. -/
theorem evenPartialTail_map {f : Color → Color} (hf : Function.Injective f) (l : List Color) :
    evenPartialTail (l.map f) = evenPartialTail l := by
  have hinj : Function.Injective (fun c => f 0 + f c) := by
    intro a b hab; exact hf (by simpa using hab)
  have h0 : (fun c => f 0 + f c) 0 = 0 := by simp
  set g : EdgePerm := ofFun (fun c => f 0 + f c) with hgdef
  have hg : ∀ c, g c = f 0 + f c := fun c => apply_ofFun_of_injective hinj h0 c
  have hmap : (l.map f).map (f 0 + ·) = l.map g := by
    rw [List.map_map]
    exact congrArg (fun h => l.map h) (funext fun c => (hg c).symm)
  calc evenPartialTail (l.map f)
      = evenNormTail (partialTrace ((l.map f).map (f 0 + ·))) := by
        rw [evenPartialTail, partialTrace_map_add]
    _ = evenNormTail (partialTrace (l.map g)) := by rw [hmap]
    _ = evenPartialTail l := by rw [partialTrace_map, evenNormTail_map, evenPartialTail]

end FourColor

import FourColor.Chromogram
import FourColor.Coloring
import FourColor.EulerTree
import FourColor.Walkup

/-!
# Kempe closure of ring traces

Three surgeries on chromograms, used to show that the ring traces of a planar
map are Kempe-closed: negating the parity of the first unmatched chord end,
turning that chord end into a chord start, and rotating a chromogram.

## Main definitions

* `gramNeg` — negate the bit of the first unmatched `pop`.
* `gramFlip` — turn the first unmatched `pop` into a `push`, inverting the
  total parity.
* `gramRot` — move the first symbol to the end, as the trace is rotated.
* `Hypermap.KempeWitness` — a chromogram matching the trace of a colouring
  along a ring, all of whose matching traces are again ring traces.  Kempe
  closure of the ring traces is exactly the existence of such a witness for
  every colouring (`Hypermap.kempeClosed_ringTrace_of_witness`).

## Main results

* `matchg_gramRot` — `gramRot` matches the rotated traces.
* `Hypermap.KempeWitness.rotate`, `Hypermap.KempeWitness.of_rotate`,
  `Hypermap.KempeWitness.of_normalised` — the reference's `without loss`
  reduction to a ring whose one-step rotation starts at a chosen dart.
* `Hypermap.exists_ring_dart` — the `Euler_tree` step selecting that dart.
* `Hypermap.contract` — the double Walkup transform contracting the edge at a
  ring dart, with `Hypermap.contractProj` its projection onto the original
  darts; `Hypermap.contractProj_edge` and `Hypermap.contractProj_node` are the
  morphism laws, and `Hypermap.contract_coloring_lift` lifts colourings back.
* `Hypermap.Kempe_map` — **the main theorem**: the ring traces of a planar plain
  quasicubic hypermap whose ring is a duplicate-free node cycle are
  Kempe-closed.
-/

namespace FourColor

/-- Negate the bit of the first unmatched `pop`, in a context of `n` open
chords. -/
def gramNegRec : ℕ → Chromogram → Chromogram
  | _, [] => []
  | n, .push :: w => .push :: gramNegRec (n + 1) w
  | n, .skip :: w => .skip :: gramNegRec n w
  | 0, .pop0 :: w => .pop1 :: w
  | 0, .pop1 :: w => .pop0 :: w
  | n + 1, .pop0 :: w => .pop0 :: gramNegRec n w
  | n + 1, .pop1 :: w => .pop1 :: gramNegRec n w

/-- Negate the bit of the first unmatched `pop`. -/
def gramNeg : Chromogram → Chromogram := gramNegRec 0

@[simp] theorem gramNegRec_nil (n : ℕ) : gramNegRec n [] = [] := rfl

@[simp] theorem gramNegRec_push (n : ℕ) (w : Chromogram) :
    gramNegRec n (.push :: w) = .push :: gramNegRec (n + 1) w := rfl

@[simp] theorem gramNegRec_skip (n : ℕ) (w : Chromogram) :
    gramNegRec n (.skip :: w) = .skip :: gramNegRec n w := rfl

@[simp] theorem gramNegRec_pop0_zero (w : Chromogram) :
    gramNegRec 0 (.pop0 :: w) = .pop1 :: w := rfl

@[simp] theorem gramNegRec_pop1_zero (w : Chromogram) :
    gramNegRec 0 (.pop1 :: w) = .pop0 :: w := rfl

@[simp] theorem gramNegRec_pop0_succ (n : ℕ) (w : Chromogram) :
    gramNegRec (n + 1) (.pop0 :: w) = .pop0 :: gramNegRec n w := rfl

@[simp] theorem gramNegRec_pop1_succ (n : ℕ) (w : Chromogram) :
    gramNegRec (n + 1) (.pop1 :: w) = .pop1 :: gramNegRec n w := rfl

/-- Negating the bit of the first unmatched chord end matches the traces that
the original chromogram matches with the opposite parity at the bottom of the
stack. -/
theorem matchg_gramNegRec : ∀ (w : Chromogram) (et : List Color) (lb : List Bool)
    (b₀ : Bool),
    matchg (lb ++ [b₀]) et (gramNegRec lb.length w) = matchg (lb ++ [!b₀]) et w := by
  intro w
  induction w with
  | nil =>
    intro et lb b₀
    cases et with
    | nil => cases lb <;> rfl
    | cons e et => rfl
  | cons s w ih =>
    intro et lb b₀
    cases et with
    | nil => cases s <;> cases lb <;> rfl
    | cons e et =>
      cases s with
      | push =>
        cases e with
        | c0 => rfl
        | c1 => rfl
        | c2 => simpa [matchg, matchStep] using ih et (false :: lb) b₀
        | c3 => simpa [matchg, matchStep] using ih et (true :: lb) b₀
      | skip =>
        cases e with
        | c0 => rfl
        | c1 => simpa [matchg, matchStep] using ih et lb b₀
        | c2 => rfl
        | c3 => rfl
      | pop0 =>
        cases lb with
        | nil => cases e <;> cases b₀ <;> rfl
        | cons b lb =>
          cases e with
          | c0 => rfl
          | c1 => rfl
          | c2 => cases b <;> simpa [matchg, matchStep] using ih et lb b₀
          | c3 => cases b <;> simpa [matchg, matchStep] using ih et lb b₀
      | pop1 =>
        cases lb with
        | nil => cases e <;> cases b₀ <;> rfl
        | cons b lb =>
          cases e with
          | c0 => rfl
          | c1 => rfl
          | c2 => cases b <;> simpa [matchg, matchStep] using ih et lb b₀
          | c3 => cases b <;> simpa [matchg, matchStep] using ih et lb b₀

/-- The one-chord case of `matchg_gramNegRec`. -/
theorem matchg_gramNeg (b₀ : Bool) (et : List Color) (w : Chromogram) :
    matchg [b₀] et (gramNeg w) = matchg [!b₀] et w :=
  matchg_gramNegRec w et [] b₀

/-- Turn the first unmatched `pop` into a `push`, adjusting the next `pop` so
that the total parity is inverted. -/
def gramFlipRec : ℕ → Chromogram → Chromogram
  | _, [] => [.push]
  | n, .push :: w => .push :: gramFlipRec (n + 1) w
  | n, .skip :: w => .skip :: gramFlipRec n w
  | 0, .pop0 :: w => .push :: gramNeg w
  | 0, .pop1 :: w => .push :: w
  | n + 1, .pop0 :: w => .pop0 :: gramFlipRec n w
  | n + 1, .pop1 :: w => .pop1 :: gramFlipRec n w

/-- Turn the first unmatched `pop` into a `push`. -/
def gramFlip : Chromogram → Chromogram := gramFlipRec 0

@[simp] theorem gramFlipRec_nil (n : ℕ) : gramFlipRec n [] = [.push] := rfl

@[simp] theorem gramFlipRec_push (n : ℕ) (w : Chromogram) :
    gramFlipRec n (.push :: w) = .push :: gramFlipRec (n + 1) w := rfl

@[simp] theorem gramFlipRec_skip (n : ℕ) (w : Chromogram) :
    gramFlipRec n (.skip :: w) = .skip :: gramFlipRec n w := rfl

@[simp] theorem gramFlipRec_pop0_zero (w : Chromogram) :
    gramFlipRec 0 (.pop0 :: w) = .push :: gramNeg w := rfl

@[simp] theorem gramFlipRec_pop1_zero (w : Chromogram) :
    gramFlipRec 0 (.pop1 :: w) = .push :: w := rfl

@[simp] theorem gramFlipRec_pop0_succ (n : ℕ) (w : Chromogram) :
    gramFlipRec (n + 1) (.pop0 :: w) = .pop0 :: gramFlipRec n w := rfl

@[simp] theorem gramFlipRec_pop1_succ (n : ℕ) (w : Chromogram) :
    gramFlipRec (n + 1) (.pop1 :: w) = .pop1 :: gramFlipRec n w := rfl

/-- Flipping the first unmatched chord end matches exactly the traces the
original chromogram matches with the two chord parities at the bottom of the
stack. -/
theorem matchg_gramFlipRec : ∀ (w : Chromogram) (et : List Color) (lb : List Bool),
    matchg lb et (gramFlipRec lb.length w) =
      (matchg (lb ++ [true, false]) et w || matchg (lb ++ [false, true]) et w) := by
  intro w
  induction w with
  | nil =>
    intro et lb
    cases et with
    | nil => cases lb <;> rfl
    | cons e et =>
      cases e <;> cases et <;> cases lb <;> rfl
  | cons s w ih =>
    intro et lb
    cases et with
    | nil => cases s <;> cases lb <;> rfl
    | cons e et =>
      cases s with
      | push =>
        cases e with
        | c0 => rfl
        | c1 => rfl
        | c2 => simpa [matchg, matchStep] using ih et (false :: lb)
        | c3 => simpa [matchg, matchStep] using ih et (true :: lb)
      | skip =>
        cases e with
        | c0 => rfl
        | c1 => simpa [matchg, matchStep] using ih et lb
        | c2 => rfl
        | c3 => rfl
      | pop0 =>
        cases lb with
        | nil =>
          cases e with
          | c0 => rfl
          | c1 => rfl
          | c2 => simpa [matchg, matchStep] using matchg_gramNeg false et w
          | c3 => simpa [matchg, matchStep] using matchg_gramNeg true et w
        | cons b lb =>
          cases e with
          | c0 => rfl
          | c1 => rfl
          | c2 => cases b <;> simpa [matchg, matchStep] using ih et lb
          | c3 => cases b <;> simpa [matchg, matchStep] using ih et lb
      | pop1 =>
        cases lb with
        | nil =>
          cases e with
          | c0 => rfl
          | c1 => rfl
          | c2 => simp [matchg, matchStep]
          | c3 => simp [matchg, matchStep]
        | cons b lb =>
          cases e with
          | c0 => rfl
          | c1 => rfl
          | c2 => cases b <;> simpa [matchg, matchStep] using ih et lb
          | c3 => cases b <;> simpa [matchg, matchStep] using ih et lb

/-- The empty-context case of `matchg_gramFlipRec`. -/
theorem matchg_gramFlip (et : List Color) (w : Chromogram) :
    matchg [] et (gramFlip w) =
      (matchg [true, false] et w || matchg [false, true] et w) :=
  matchg_gramFlipRec w et []

/-! ### Rotation -/

/-- Move the first symbol of a chromogram to the end, turning a `push` into a
`pop` (and flipping the matching `pop`, via `gramFlip`). -/
def gramRotAux : Chromogram → Chromogram
  | [] => []
  | .push :: w => gramFlip (w ++ [.pop1])
  | .skip :: w => w ++ [.skip]
  | .pop0 :: w => .pop0 :: w
  | .pop1 :: w => .pop1 :: w

@[simp] theorem gramRotAux_nil : gramRotAux [] = [] := rfl

@[simp] theorem gramRotAux_push (w : Chromogram) :
    gramRotAux (.push :: w) = gramFlip (w ++ [.pop1]) := rfl

@[simp] theorem gramRotAux_skip (w : Chromogram) :
    gramRotAux (.skip :: w) = w ++ [.skip] := rfl

@[simp] theorem gramRotAux_pop0 (w : Chromogram) :
    gramRotAux (.pop0 :: w) = .pop0 :: w := rfl

@[simp] theorem gramRotAux_pop1 (w : Chromogram) :
    gramRotAux (.pop1 :: w) = .pop1 :: w := rfl

/-- Rotate a chromogram, so that it matches the left rotation of exactly the
traces the original matched.  Imbalanced chromograms are left alone: they match
nothing, so matching is preserved trivially. -/
def gramRot (w : Chromogram) : Chromogram :=
  if balanced 0 false w || balanced 0 true w then gramRotAux w else w

/-- A matched chromogram is balanced at depth `0`, for one of the two
parities. -/
theorem balanced_of_matchg {et : List Color} {w : Chromogram} (h : matchg [] et w) :
    balanced 0 false w || balanced 0 true w := by
  have hb := (matchg_balanced h).2
  cases hs : et.sum.lo with
  | false => rw [hs] at hb; simp [hb]
  | true => rw [hs] at hb; simp [hb]

/-- An imbalanced chromogram matches nothing. -/
theorem matchg_eq_false_of_not_balanced {w : Chromogram}
    (hw : (balanced 0 false w || balanced 0 true w) = false) (et : List Color) :
    matchg [] et w = false := by
  cases h : matchg [] et w with
  | false => rfl
  | true => rw [balanced_of_matchg h] at hw; simp at hw

/-- A chromogram whose last symbol has been restored is never empty. -/
theorem gramFlipRec_ne_nil (n : ℕ) (w : Chromogram) : gramFlipRec n w ≠ [] := by
  cases w with
  | nil => simp
  | cons s w => cases n <;> cases s <;> simp

theorem gramRotAux_ne_nil {w : Chromogram} (hw : w ≠ []) : gramRotAux w ≠ [] := by
  cases w with
  | nil => exact absurd rfl hw
  | cons s w => cases s <;> simp [gramFlip, gramFlipRec_ne_nil]

/-- A one-colour trace never matches a word of length at least two. -/
theorem matchg_singleton_cons_append (lb : List Bool) (c : Color) (s s' : GramSymbol)
    (w : Chromogram) : matchg lb [c] (s :: (w ++ [s'])) = false := by
  cases w with
  | nil => exact matchg_singleton_of_cons_cons lb c s s' []
  | cons a w' => exact matchg_singleton_of_cons_cons lb c s a (w' ++ [s'])

/-- Appending a `skip` to a chromogram matches appending the colour `c1` to the
trace. -/
theorem matchg_append_skip : ∀ (w : Chromogram) (lb : List Bool) (et : List Color)
    (e : Color),
    matchg lb (et ++ [e]) (w ++ [.skip]) = ((e == Color.c1) && matchg lb et w) := by
  intro w
  induction w with
  | nil =>
    intro lb et e
    cases et with
    | nil => cases e <;> simp [matchStep]
    | cons e' et =>
      simp only [List.nil_append, List.cons_append, matchg_cons]
      cases e' <;> simp [matchStep]
  | cons s w ih =>
    intro lb et e
    cases et with
    | nil =>
      simp only [List.nil_append, List.cons_append]
      rw [matchg_singleton_cons_append]
      simp
    | cons e' et =>
      simp only [List.cons_append, matchg_cons]
      cases hs : matchStep e' s lb with
      | none => simp
      | some lb' => simpa using ih lb' et e

/-- Appending a `pop1` to a chromogram that is balanced above the bottom of the
stack matches appending, to the trace, the colour that closes the bottom
chord. -/
theorem matchg_append_pop1 : ∀ (w : Chromogram) (lb : List Bool) (b b₀ : Bool)
    (et : List Color) (e : Color), balanced lb.length b₀ w →
    matchg (lb ++ [b]) (et ++ [e]) (w ++ [.pop1]) =
      ((e == Color.ofBits true (!b)) && matchg lb et w) := by
  intro w
  induction w with
  | nil =>
    intro lb b b₀ et e hbal
    simp only [balanced_nil, Bool.and_eq_true, beq_iff_eq] at hbal
    obtain rfl : lb = [] := List.length_eq_zero_iff.mp hbal.1
    cases et with
    | nil => cases e <;> cases b <;> simp [matchStep, Color.ofBits]
    | cons e' et =>
      simp only [List.nil_append, List.cons_append, matchg_cons]
      cases e' <;> cases b <;> simp [matchStep]
  | cons s w ih =>
    intro lb b b₀ et e hbal
    cases et with
    | nil =>
      simp only [List.nil_append, List.cons_append]
      rw [matchg_singleton_cons_append]
      simp
    | cons e' et =>
      cases s with
      | push =>
        rw [balanced_push] at hbal
        cases e' with
        | c0 => simp [matchStep]
        | c1 => simp [matchStep]
        | c2 =>
          simpa [matchStep] using ih (false :: lb) b b₀ et e (by simpa using hbal)
        | c3 =>
          simpa [matchStep] using ih (true :: lb) b b₀ et e (by simpa using hbal)
      | skip =>
        rw [balanced_skip] at hbal
        cases e' with
        | c0 => simp [matchStep]
        | c1 => simpa [matchStep] using ih lb b (!b₀) et e hbal
        | c2 => simp [matchStep]
        | c3 => simp [matchStep]
      | pop0 =>
        cases lb with
        | nil => simp at hbal
        | cons b' lb =>
          rw [List.length_cons, balanced_pop0_succ] at hbal
          cases e' <;> cases b' <;>
            simp_all [matchStep, ih lb b b₀ et e hbal]
      | pop1 =>
        cases lb with
        | nil => simp at hbal
        | cons b' lb =>
          rw [List.length_cons, balanced_pop1_succ] at hbal
          cases e' <;> cases b' <;>
            simp_all [matchStep, ih lb b (!b₀) et e hbal]

/-- `gramRot` matches the left rotation of exactly the traces matched by the
original chromogram. -/
theorem matchg_gramRot (et : List Color) (w : Chromogram) :
    matchg [] (et.rotate 1) (gramRot w) = matchg [] et w := by
  cases hb : balanced 0 false w || balanced 0 true w with
  | false =>
    have hg : gramRot w = w := by simp [gramRot, hb]
    rw [hg, matchg_eq_false_of_not_balanced hb, matchg_eq_false_of_not_balanced hb]
  | true =>
    have hg : gramRot w = gramRotAux w := by simp [gramRot, hb]
    rw [hg]
    cases et with
    | nil =>
      rw [List.rotate_nil]
      cases w with
      | nil => simp
      | cons s w =>
        obtain ⟨s', w', hw'⟩ :=
          List.exists_cons_of_ne_nil (gramRotAux_ne_nil (w := s :: w) (by simp))
        rw [hw']
        simp
    | cons e et =>
      rw [List.rotate_cons_succ, List.rotate_zero]
      cases w with
      | nil => simp
      | cons s w =>
        cases s with
        | push =>
          rw [balanced_push, balanced_push] at hb
          obtain ⟨b₀, hb₀⟩ : ∃ b₀, balanced ([true] : List Bool).length b₀ w := by
            rcases Bool.or_eq_true_iff.mp hb with h | h
            exacts [⟨false, h⟩, ⟨true, h⟩]
          have h1 := matchg_append_pop1 w [true] false b₀ et e hb₀
          have h2 := matchg_append_pop1 w [false] true b₀ et e (by simpa using hb₀)
          simp only [List.cons_append, List.nil_append] at h1 h2
          rw [gramRotAux_push, matchg_gramFlip, h1, h2]
          cases e <;> simp [matchStep, Color.ofBits]
        | skip =>
          rw [gramRotAux_skip, matchg_append_skip w [] et e]
          cases e <;> simp [matchStep]
        | pop0 => simp at hb
        | pop1 => simp at hb

/-! ### Ring traces -/

namespace Hypermap

variable {D : Type*} {G : Hypermap D}

/-- The set of ring traces is closed under colour permutations. -/
theorem RingTrace.map {r : List D} {et : List Color} (h : G.RingTrace r et)
    (g : EdgePerm) : G.RingTrace r (et.map g) := by
  obtain ⟨k, hk, rfl⟩ := h
  refine ⟨(g : Color → Color) ∘ k, hk.comp (EdgePerm.apply_injective g), ?_⟩
  rw [← List.map_map, trace_map]

/-- The Kempe-closure witness for a ring and a colouring: a chromogram matching
the trace of `k` along `r`, all of whose matching traces are ring traces. -/
def KempeWitness (G : Hypermap D) (r : List D) (k : D → Color) : Prop :=
  ∃ w, matchg [] (trace (r.map k)) w ∧ ∀ et', matchg [] et' w → G.RingTrace r et'

/-- Every list of colours is a one-step rotation. -/
theorem exists_rotate_one (et : List Color) : ∃ es : List Color, et = es.rotate 1 := by
  refine ⟨et.rotate (et.length - 1), ?_⟩
  rw [List.rotate_rotate]
  cases et with
  | nil => simp
  | cons e et =>
    have : (e :: et).length - 1 + 1 = (e :: et).length := by simp
    rw [this, List.rotate_length]

/-- A Kempe witness for `r` rotates to one for `r.rotate 1`. -/
theorem KempeWitness.rotate_one {r : List D} {k : D → Color}
    (h : G.KempeWitness r k) : G.KempeWitness (r.rotate 1) k := by
  obtain ⟨w, hw, hw'⟩ := h
  refine ⟨gramRot w, ?_, ?_⟩
  · rw [List.map_rotate, trace_rotate, matchg_gramRot]
    exact hw
  · intro et' het'
    obtain ⟨es, rfl⟩ := exists_rotate_one et'
    rw [matchg_gramRot] at het'
    obtain ⟨k', hk', rfl⟩ := hw' es het'
    exact ⟨k', hk', by rw [List.map_rotate, trace_rotate]⟩

/-- A Kempe witness for `r` rotates to one for any rotation of `r`. -/
theorem KempeWitness.rotate {r : List D} {k : D → Color} (h : G.KempeWitness r k) :
    ∀ n, G.KempeWitness (r.rotate n) k := by
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih => simpa [← List.rotate_rotate] using ih.rotate_one

/-! ### Rotating the geometrical hypotheses -/

theorem Quasicubic.rotate {r : List D} (h : G.Quasicubic r) (n : ℕ) :
    G.Quasicubic (r.rotate n) := by
  constructor
  · intro x hx
    exact h.node_node_node (by simpa [List.mem_rotate] using hx)
  · intro x hx
    exact h.node_ne (by simpa [List.mem_rotate] using hx)

theorem PlainQuasicubic.rotate {r : List D} (h : G.PlainQuasicubic r) (n : ℕ) :
    G.PlainQuasicubic (r.rotate n) := ⟨h.plain, h.quasicubic.rotate n⟩

theorem UcyclePlainQuasicubic.rotate {r : List D} (h : G.UcyclePlainQuasicubic r) (n : ℕ) :
    G.UcyclePlainQuasicubic (r.rotate n) :=
  ⟨h.base.rotate n, isCyclicChain_rotate.mpr h.cycle, List.nodup_rotate.mpr h.nodup⟩

theorem UcyclePlanarPlainQuasicubic.rotate {r : List D}
    (h : G.UcyclePlanarPlainQuasicubic r) (n : ℕ) :
    G.UcyclePlanarPlainQuasicubic (r.rotate n) := ⟨h.base.rotate n, h.planar⟩

end Hypermap

/-! ### Reductions for the Kempe closure theorem

The main theorem states that the ring traces of a planar plain quasicubic
hypermap whose ring is a node cycle are Kempe-closed.  The results below carry
out its first reductions: the closure property splits into the (immediate)
stability under colour permutations and the existence of a Kempe witness, the
witness may be transported along an arbitrary rotation of the ring, and the
reference's `Euler_tree` selects the ring dart at which the induction cuts. -/

namespace Hypermap

variable {D : Type*} {G : Hypermap D}

/-- Kempe closure of the ring traces follows from a Kempe witness for every
colouring. -/
theorem kempeClosed_ringTrace_of_witness (G : Hypermap D) (r : List D)
    (h : ∀ k : D → Color, G.Coloring k → G.KempeWitness r k) :
    KempeClosed (G.RingTrace r) := by
  intro et het
  refine ⟨fun g => het.map g, ?_⟩
  obtain ⟨k, hk, rfl⟩ := het
  exact h k hk

/-- Rotating a list backwards: every rotation has an inverse rotation. -/
theorem exists_rotate_inv {α : Type*} (l : List α) (i : ℕ) :
    ∃ m, (l.rotate i).rotate m = l := by
  cases l with
  | nil => exact ⟨0, by simp⟩
  | cons a t =>
    set l : List α := a :: t with hl
    have hpos : 0 < l.length := by simp [hl]
    have hmod := Nat.div_add_mod i l.length
    have hlt : i % l.length < l.length := Nat.mod_lt _ hpos
    refine ⟨l.length - i % l.length, ?_⟩
    rw [List.rotate_rotate]
    have h : i + (l.length - i % l.length) = l.length * (i / l.length) + l.length := by omega
    rw [h, ← Nat.mul_succ, rotate_length_mul]

/-- A Kempe witness for some rotation of the ring is one for the ring. -/
theorem KempeWitness.of_rotate {r : List D} {k : D → Color} (i : ℕ)
    (h : G.KempeWitness (r.rotate i) k) : G.KempeWitness r k := by
  obtain ⟨m, hm⟩ := exists_rotate_inv r i
  have h' := h.rotate m
  rwa [hm] at h'

/-- The reference's `rot_to`: a rotation brings any member to the head. -/
theorem exists_rotate_eq_cons {α : Type*} {l : List α} {z : α} (hz : z ∈ l) :
    ∃ i p, l.rotate i = z :: p := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hz
  refine ⟨l₁.length, l₂ ++ l₁, ?_⟩
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

/-- A rotation brings any member to the second place. -/
theorem exists_rotate_rotate_one_eq_cons {α : Type*} {l : List α} {z : α} (hz : z ∈ l) :
    ∃ i p, (l.rotate i).rotate 1 = z :: p := by
  obtain ⟨j, p, hj⟩ := exists_rotate_eq_cons hz
  have hpos : 0 < l.length := List.length_pos_of_mem hz
  have hlen : (z :: p).length = l.length := by rw [← hj]; simp
  refine ⟨j + (l.length - 1), p, ?_⟩
  have h1 : j + (l.length - 1) + 1 = j + l.length := by omega
  rw [List.rotate_rotate, h1, ← List.rotate_rotate, hj, ← hlen, List.rotate_length]

/-- **The `without loss` normalisation.**  To find a Kempe witness for a ring it
suffices to find one for the rotations of the ring whose one-step rotation
starts at a prescribed dart of the ring. -/
theorem KempeWitness.of_normalised {r : List D} {k : D → Color} {z : D} (hz : z ∈ r)
    (H : ∀ (i : ℕ) (p : List D), (r.rotate i).rotate 1 = z :: p →
      G.KempeWitness (r.rotate i) k) : G.KempeWitness r k := by
  obtain ⟨i, p, hi⟩ := exists_rotate_rotate_one_eq_cons hz
  exact (H i p hi).of_rotate i

/-- The empty ring has the empty chromogram as a Kempe witness. -/
theorem kempeWitness_nil {k : D → Color} (hk : G.Coloring k) : G.KempeWitness [] k := by
  refine ⟨[], by simp [trace], ?_⟩
  intro et' het'
  obtain rfl : et' = [] := by
    cases et' with
    | nil => rfl
    | cons e et => simp at het'
  exact ⟨k, hk, by simp [trace]⟩

/-- A colouring forbids fixed darts of `node`: this is the reference's `n'id`. -/
theorem Coloring.node_ne {k : D → Color} (hk : G.Coloring k) (x : D) : G.node x ≠ x := by
  intro hx
  refine hk.edge (G.node x) ?_
  have h1 : k (G.edge (G.node x)) = k x := by
    rw [← hk.face (G.edge (G.node x)), G.nodeK]
  rw [h1, hx]

/-- **The `Euler_tree` step.**  In a planar plain hypermap, a node cycle `r`
contains a dart `z` whose face is degenerate or leaves the cycle.  This is the
dart at which the induction of the Kempe closure theorem contracts. -/
theorem exists_ring_dart [Finite D] {G : Hypermap D} {r : List D}
    (hplanar : G.Planar) (hplain : G.Plain)
    (hcyc : IsCyclicChain (fun u v => v = G.node u) r) {x : D} (hx : x ∈ r) :
    ∃ z ∈ r, G.face z = z ∨ G.face z ∉ r := by
  have hJ : G.permN.Jordan := ((planar_permN (G := G)).mpr hplanar).jordan
  obtain ⟨y, hxy, hy⟩ := Hypermap.exists_degenerate_or_not_cross (G := G.permN) hJ x
  have hxy' : G.CNode x y := hxy
  have hyr : y ∈ r := (cnode_iff_mem hcyc hx y).mp hxy'
  refine ⟨y, hyr, ?_⟩
  rcases hy with hy | hy
  · rcases hy with hy | hy
    · exact Or.inl hy.symm
    · exact absurd hy (hplain.edge_ne y)
  · exact Or.inr fun hmem => hy ((cnode_iff_mem hcyc hyr (G.face y)).mpr hmem)

end Hypermap

/-! ### The double Walkup contraction

The induction step of the Kempe closure theorem contracts the edge `{z, edge z}`
of a plain hypermap: first delete `z` with `walkupN`, then delete the image of
`edge z` with `walkupE`.  The resulting map projects onto the original darts
other than `z` and `edge z`, and the projection commutes with `edge`; it
commutes with `node` too, except that `node` jumps over the two deleted darts,
exchanging their `node` images. -/

namespace Hypermap

section Contract

variable {D : Type*} [DecidableEq D] {G : Hypermap D} {z : D}

/-- The other end of the edge at `z`, as a dart of the first Walkup transform. -/
def contractDart (G : Hypermap D) (z : D) (hez : G.edge z ≠ z) : Walkup G z := ⟨G.edge z, hez⟩

/-- The double Walkup transform contracting the edge `{z, edge z}`. -/
def contract (G : Hypermap D) (z : D) (hez : G.edge z ≠ z) :
    Hypermap (Walkup (G.walkupN z) (contractDart G z hez)) :=
  (G.walkupN z).walkupE (contractDart G z hez)

variable {hez : G.edge z ≠ z}

/-- The projection of the contracted map onto the darts of the original. -/
def contractProj (u : Walkup (G.walkupN z) (contractDart G z hez)) : D := u.val.val

theorem contractProj_ne_z (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    contractProj u ≠ z := u.val.2

theorem contractProj_ne_ez (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    contractProj u ≠ G.edge z := fun hc => u.2 (Subtype.ext hc)

theorem contractProj_injective :
    Function.Injective (contractProj (G := G) (z := z) (hez := hez)) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

/-- Every dart other than `z` and `edge z` comes from the contracted map. -/
def contractLift {x : D} (hx : x ≠ z) (hx' : x ≠ G.edge z) :
    Walkup (G.walkupN z) (contractDart G z hez) :=
  ⟨⟨x, hx⟩, fun hc => hx' (congrArg Subtype.val hc)⟩

@[simp] theorem contractProj_contractLift {x : D} (hx : x ≠ z) (hx' : x ≠ G.edge z) :
    contractProj (contractLift (hez := hez) hx hx') = x := rfl

/-- The deleted dart is a fixed point of the first transform's edge map. -/
theorem walkupN_edge_contractDart (hee : G.edge (G.edge z) = z) :
    (G.walkupN z).edge (contractDart G z hez) = contractDart G z hez :=
  Subtype.ext (skip_val_of_eq (f := G.edge) (u := contractDart G z hez) hee)

theorem contract_edge (hee : G.edge (G.edge z) = z) :
    (contract G z hez).edge = skip ((G.walkupN z).edge) (contractDart G z hez) :=
  walkupE_edge_of_glink (G.walkupN z) (contractDart G z hez)
    (Or.inl (walkupN_edge_contractDart hee).symm)

theorem contract_edge_val (hee : G.edge (G.edge z) = z)
    (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    ((contract G z hez).edge u).val = skip G.edge z u.val := by
  have key : skipFun ((G.walkupN z).edge) (contractDart G z hez) u.val
      = (G.walkupN z).edge u.val := by
    unfold skipFun
    split
    · rename_i hc
      rw [walkupN_edge_contractDart hee]
      exact hc.symm
    · rfl
  rw [contract_edge hee, skip_val]
  exact key

/-- The projection commutes with `edge`. -/
theorem contractProj_edge (hee : G.edge (G.edge z) = z)
    (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    contractProj ((contract G z hez).edge u) = G.edge (contractProj u) := by
  have hne : G.edge (contractProj u) ≠ z := fun hcon =>
    contractProj_ne_ez u (G.edge.injective (hee.trans hcon.symm)).symm
  show ((contract G z hez).edge u).val.val = _
  rw [contract_edge_val hee]
  exact skip_val_of_ne hne

/-- The projection commutes with `node`, up to the jump over the two deleted
darts: `z` is replaced by `node (edge z)` and `edge z` by `node z`. -/
theorem contractProj_node (hp : G.Plain) (hnid : ∀ x : D, G.node x ≠ x)
    (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    contractProj ((contract G z hez).node u) =
      if G.node (contractProj u) = z then G.node (G.edge z)
      else if G.node (contractProj u) = G.edge z then G.node z
      else G.node (contractProj u) := by
  have hee : G.edge (G.edge z) = z := hp.edge_edge z
  have hinv : ∀ x y : D, G.edge x = y ↔ x = G.edge y := fun x y =>
    ⟨fun h => by rw [← h, hp.edge_edge], fun h => by rw [h, hp.edge_edge]⟩
  have hu1 : contractProj u ≠ z := contractProj_ne_z u
  have hu2 : contractProj u ≠ G.edge z := contractProj_ne_ez u
  have hbase : ((contract G z hez).node u).val =
      skipFun ((G.walkupN z).node) (contractDart G z hez) u.val := rfl
  have hval : ∀ v : Walkup G z, (G.walkupN z).node u.val = v →
      v ≠ contractDart G z hez →
      contractProj ((contract G z hez).node u) = v.val := by
    intro v hv hne
    show ((contract G z hez).node u).val.val = v.val
    rw [hbase]
    unfold skipFun
    rw [hv, ite_eq_right hne]
  have hvalz : (G.walkupN z).node u.val = contractDart G z hez →
      ∀ v : Walkup G z, (G.walkupN z).node (contractDart G z hez) = v →
      contractProj ((contract G z hez).node u) = v.val := by
    intro hv v hv2
    show ((contract G z hez).node u).val.val = v.val
    rw [hbase]
    unfold skipFun
    rw [hv, ite_eq_left rfl, hv2]
  by_cases hc : G.node (contractProj u) = z
  · rw [ite_eq_left hc]
    have hnez : G.node (G.edge z) ≠ z := fun hcon =>
      hu2 (G.node.injective (hc.trans hcon.symm))
    have heu : G.edge (G.node (G.edge z)) ≠ z := fun hcon =>
      hnid (G.edge z) ((hinv _ _).mp hcon)
    exact hvalz (walkupN_node_eq_edge G z hee hc hez) _
      (walkupN_node_eq_of G z (u := contractDart G z hez) hnez heu)
  · rw [ite_eq_right hc]
    by_cases hc2 : G.node (contractProj u) = G.edge z
    · rw [ite_eq_left hc2]
      have hfz : contractProj u = G.face z :=
        G.node.injective (hc2.trans (hp.node_face z).symm)
      have hnz : G.node z ≠ z := hnid z
      have hnz2 : G.node z ≠ G.edge z := by
        intro hcon
        have hfzz : G.face z = z := by
          have h := G.nodeK z
          rw [hcon, hee] at h
          exact h
        exact hu1 (hfz.trans hfzz)
      have h1 : G.edge (G.node z) ≠ z := fun hcon => hnz2 ((hinv _ _).mp hcon)
      have h2 : G.face (G.edge (G.node z)) = z := G.nodeK z
      have hne : (⟨G.node z, hnz⟩ : Walkup G z) ≠ contractDart G z hez := fun hcon =>
        hnz2 (congrArg Subtype.val hcon)
      exact hval ⟨G.node z, hnz⟩
        (walkupN_node_eq_jump G z (u := ⟨G.node z, hnz⟩) (v := u.val) h1 h2 hfz) hne
    · rw [ite_eq_right hc2]
      have heu : G.edge (G.node (contractProj u)) ≠ z := fun hcon =>
        hc2 ((hinv _ _).mp hcon)
      have hne : (⟨G.node (contractProj u), hc⟩ : Walkup G z) ≠ contractDart G z hez :=
        fun hcon => hc2 (congrArg Subtype.val hcon)
      exact hval ⟨G.node (contractProj u), hc⟩
        (walkupN_node_eq_of G z (u := u.val) hc heu) hne

/-- The contracted map is plain. -/
theorem contract_plain (hp : G.Plain) : (contract G z hez).Plain := by
  have hee := hp.edge_edge z
  constructor
  · intro u
    refine contractProj_injective ?_
    rw [contractProj_edge hee, contractProj_edge hee, hp.edge_edge]
  · intro u hcon
    refine hp.edge_ne (contractProj u) ?_
    rw [← contractProj_edge hee, hcon]

/-- The projection of `face` in the contracted map: it agrees with `face`
except that it jumps over the two deleted darts. -/
theorem contractProj_face (hp : G.Plain) (hnid : ∀ x : D, G.node x ≠ x)
    (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    contractProj ((contract G z hez).face u) =
      if G.face (contractProj u) = z ∨ G.face (contractProj u) = G.edge z
      then G.face (G.face (contractProj u)) else G.face (contractProj u) := by
  have hee := hp.edge_edge z
  have hfk : (contract G z hez).edge ((contract G z hez).node ((contract G z hez).face u)) = u :=
    (contract G z hez).faceK u
  have h1 : G.edge (contractProj ((contract G z hez).node ((contract G z hez).face u)))
      = contractProj u := by
    rw [← contractProj_edge hee, hfk]
  rw [contractProj_node hp hnid ((contract G z hez).face u)] at h1
  by_cases hc : G.node (contractProj ((contract G z hez).face u)) = z
  · rw [ite_eq_left hc] at h1
    have hYv : contractProj ((contract G z hez).face u) = G.face (G.edge z) :=
      G.node.injective (hc.trans (G.edgeK z).symm)
    have hfu : G.face (contractProj u) = G.edge z := by rw [← h1, G.nodeK]
    rw [ite_eq_left (Or.inr hfu), hfu, ← hYv]
  · rw [ite_eq_right hc] at h1
    by_cases hc2 : G.node (contractProj ((contract G z hez).face u)) = G.edge z
    · rw [ite_eq_left hc2] at h1
      have hYv : contractProj ((contract G z hez).face u) = G.face z :=
        G.node.injective (hc2.trans (hp.node_face z).symm)
      have hfu : G.face (contractProj u) = z := by rw [← h1, G.nodeK]
      rw [ite_eq_left (Or.inl hfu), hfu, ← hYv]
    · rw [ite_eq_right hc2] at h1
      have hfu : G.face (contractProj u) = contractProj ((contract G z hez).face u) := by
        rw [← h1, G.nodeK]
      have hne1 : contractProj ((contract G z hez).face u) ≠ z :=
        contractProj_ne_z ((contract G z hez).face u)
      have hne2 : contractProj ((contract G z hez).face u) ≠ G.edge z :=
        contractProj_ne_ez ((contract G z hez).face u)
      rw [ite_eq_right (by rw [hfu]; exact fun h => h.elim hne1 hne2), hfu]

/-- Restricting a colouring of the original map along the projection colours the
contracted map. -/
theorem contract_coloring (hp : G.Plain) (hnid : ∀ x : D, G.node x ≠ x)
    {k : D → Color} (hk : G.Coloring k) :
    (contract G z hez).Coloring (k ∘ contractProj) := by
  have hee := hp.edge_edge z
  have hkey : ∀ x : D, k (G.edge (G.node x)) = k x := fun x => by
    rw [← hk.face (G.edge (G.node x)), G.nodeK]
  constructor
  · intro u
    show k (contractProj ((contract G z hez).edge u)) ≠ k (contractProj u)
    rw [contractProj_edge hee]
    exact hk.edge _
  · intro u
    show k (contractProj ((contract G z hez).face u)) = k (contractProj u)
    have hfk : (contract G z hez).edge
        ((contract G z hez).node ((contract G z hez).face u)) = u :=
      (contract G z hez).faceK u
    have h1 : G.edge (contractProj ((contract G z hez).node ((contract G z hez).face u)))
        = contractProj u := by
      rw [← contractProj_edge hee, hfk]
    rw [contractProj_node hp hnid ((contract G z hez).face u)] at h1
    rw [← h1]
    by_cases hc : G.node (contractProj ((contract G z hez).face u)) = z
    · rw [ite_eq_left hc, hkey]
      have hYv : contractProj ((contract G z hez).face u) = G.face (G.edge z) :=
        G.node.injective (hc.trans (G.edgeK z).symm)
      rw [hYv, hk.face]
    · rw [ite_eq_right hc]
      by_cases hc2 : G.node (contractProj ((contract G z hez).face u)) = G.edge z
      · rw [ite_eq_left hc2, hkey]
        have hYv : contractProj ((contract G z hez).face u) = G.face z :=
          G.node.injective (hc2.trans (hp.node_face z).symm)
        rw [hYv, hk.face]
      · rw [ite_eq_right hc2, hkey]

/-! ### Lifting a colouring back across the contraction -/

/-- Extend a colouring of the contracted map to the original darts, giving the
two deleted darts the prescribed colours. -/
def contractExtend (k1 : Walkup (G.walkupN z) (contractDart G z hez) → Color)
    (cz cez : Color) (x : D) : Color :=
  if hx : x = z then cz else if hx' : x = G.edge z then cez else k1 (contractLift hx hx')

variable {k1 : Walkup (G.walkupN z) (contractDart G z hez) → Color} {cz cez : Color}

@[simp] theorem contractExtend_z : contractExtend k1 cz cez z = cz := by
  unfold contractExtend; rw [dite_eq_left rfl]

@[simp] theorem contractExtend_ez : contractExtend (hez := hez) k1 cz cez (G.edge z) = cez := by
  unfold contractExtend; rw [dite_eq_right hez, dite_eq_left rfl]

theorem contractExtend_of_ne {x : D} (hx : x ≠ z) (hx' : x ≠ G.edge z) :
    contractExtend k1 cz cez x = k1 (contractLift hx hx') := by
  unfold contractExtend; rw [dite_eq_right hx, dite_eq_right hx']

@[simp] theorem contractExtend_contractProj
    (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    contractExtend k1 cz cez (contractProj u) = k1 u := by
  rw [contractExtend_of_ne (contractProj_ne_z u) (contractProj_ne_ez u)]
  exact congrArg k1 (Subtype.ext (Subtype.ext rfl))

/-- **Lifting a colouring.**  A colouring of the contracted map extends to a
colouring of the original one as soon as the two colours given to the deleted
darts differ and agree with the colours of the faces they belong to. -/
theorem contract_coloring_lift (hp : G.Plain) (hnid : ∀ x : D, G.node x ≠ x)
    (hk1 : (contract G z hez).Coloring k1) (hne : cz ≠ cez)
    (hfz : contractExtend k1 cz cez (G.face z) = cz)
    (hfez : contractExtend k1 cz cez (G.face (G.edge z)) = cez) :
    G.Coloring (contractExtend k1 cz cez) := by
  have hee := hp.edge_edge z
  constructor
  · intro x
    by_cases hx : x = z
    · subst hx
      rw [contractExtend_ez, contractExtend_z]
      exact fun h => hne h.symm
    · by_cases hx' : x = G.edge z
      · subst hx'
        rw [hee, contractExtend_z, contractExtend_ez]
        exact hne
      · have he1 : G.edge x ≠ z := fun h =>
          hx' (G.edge.injective (hee.trans h.symm)).symm
        have he2 : G.edge x ≠ G.edge z := fun h => hx (G.edge.injective h)
        rw [contractExtend_of_ne he1 he2, contractExtend_of_ne hx hx']
        have hlift : contractLift (hez := hez) he1 he2
            = (contract G z hez).edge (contractLift hx hx') := by
          refine contractProj_injective ?_
          rw [contractProj_edge hee]
          simp
        rw [hlift]
        exact hk1.edge _
  · intro x
    by_cases hx : x = z
    · subst hx; rw [contractExtend_z]; exact hfz
    · by_cases hx' : x = G.edge z
      · subst hx'; rw [contractExtend_ez]; exact hfez
      · have hface := contractProj_face (hez := hez) hp hnid (contractLift hx hx')
        rw [contractProj_contractLift] at hface
        have hproj : contractExtend k1 cz cez
              (contractProj ((contract G z hez).face (contractLift hx hx')))
            = k1 (contractLift hx hx') := by
          rw [contractExtend_contractProj, hk1.face]
        rw [hface] at hproj
        rw [contractExtend_of_ne hx hx']
        by_cases hc : G.face x = z ∨ G.face x = G.edge z
        · rw [ite_eq_left hc] at hproj
          rcases hc with hc | hc
          · rw [hc] at hproj ⊢
            rw [contractExtend_z, ← hfz]
            exact hproj
          · rw [hc] at hproj ⊢
            rw [contractExtend_ez, ← hfez]
            exact hproj
        · rw [ite_eq_right hc] at hproj
          exact hproj

/-- The contracted map is planar. -/
theorem contract_planar [Fintype D] (hplanar : G.Planar) : (contract G z hez).Planar :=
  planar_walkupE (G.walkupN z) (contractDart G z hez) (planar_walkupN G z hplanar)

/-! ### Lifting lists of darts -/

/-- `node` as seen through the contraction: it jumps over the two deleted
darts, exchanging their `node` images. -/
def adjNode (G : Hypermap D) (z x : D) : D :=
  if G.node x = z then G.node (G.edge z)
  else if G.node x = G.edge z then G.node z else G.node x

theorem adjNode_eq_node {x : D} (h1 : G.node x ≠ z) (h2 : G.node x ≠ G.edge z) :
    adjNode G z x = G.node x := by
  unfold adjNode; rw [ite_eq_right h1, ite_eq_right h2]

theorem adjNode_of_node_eq_z {x : D} (h : G.node x = z) :
    adjNode G z x = G.node (G.edge z) := by
  unfold adjNode; rw [ite_eq_left h]

theorem adjNode_of_node_eq_ez {x : D} (h1 : G.node x ≠ z) (h2 : G.node x = G.edge z) :
    adjNode G z x = G.node z := by
  unfold adjNode; rw [ite_eq_right h1, ite_eq_left h2]

theorem contractProj_adjNode (hp : G.Plain) (hnid : ∀ x : D, G.node x ≠ x)
    (u : Walkup (G.walkupN z) (contractDart G z hez)) :
    contractProj ((contract G z hez).node u) = adjNode G z (contractProj u) :=
  contractProj_node hp hnid u

/-- Any list of darts avoiding the two deleted ones is the projection of a list
of darts of the contracted map. -/
theorem exists_lift_list : ∀ (q : List D), (∀ x ∈ q, x ≠ z ∧ x ≠ G.edge z) →
    ∃ s : List (Walkup (G.walkupN z) (contractDart G z hez)), s.map contractProj = q := by
  intro q
  induction q with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons x q ih =>
    intro hq
    obtain ⟨s, hs⟩ := ih fun y hy => hq y (List.mem_cons_of_mem _ hy)
    obtain ⟨hx1, hx2⟩ := hq x List.mem_cons_self
    exact ⟨contractLift hx1 hx2 :: s, by simp [hs]⟩

end Contract

end Hypermap

/-- A cyclic chain transfers backwards along a map. -/
theorem isCyclicChain_of_map {α β : Type*} {f : α → β} {e : α → α → Prop} {e' : β → β → Prop}
    (hf : ∀ x y : α, e' (f x) (f y) → e x y) {l : List α}
    (hl : IsCyclicChain e' (l.map f)) : IsCyclicChain e l := by
  refine ⟨List.isChain_of_isChain_map f hf hl.1, ?_⟩
  intro x hx y hy
  rw [Option.mem_def] at hx hy
  refine hf x y (hl.2 (f x) ?_ (f y) ?_) <;> rw [Option.mem_def]
  · simp [hx]
  · simp [hy]

namespace Hypermap

/-! ### Kempe witnesses in the rotated-trace form -/

variable {E : Type*} {H : Hypermap E}

/-- Every list is the one-step rotation of one of its own rotations. -/
theorem exists_rotate_succ {α : Type*} (l : List α) : ∃ n, (l.rotate n).rotate 1 = l := by
  cases l with
  | nil => exact ⟨0, by simp⟩
  | cons a t =>
    refine ⟨(a :: t).length - 1, ?_⟩
    rw [List.rotate_rotate]
    have h : (a :: t).length - 1 + 1 = (a :: t).length := by simp
    rw [h, List.rotate_length]

theorem trace_map_of_rotate_one {α : Type*} {l m : List α} (h : l.rotate 1 = m)
    (k : α → Color) : trace (l.map k) = rotTrace (m.map k) := by
  rw [← h, List.map_rotate, rotTrace_rotate_one]

/-- The Kempe witness property stated for the rotated trace, which is the form
in which the induction hypothesis is used. -/
def RotKempeWitness (H : Hypermap E) (s : List E) (k : E → Color) : Prop :=
  ∃ w, matchg [] (rotTrace (s.map k)) w ∧
    ∀ et', matchg [] et' w → ∃ k', H.Coloring k' ∧ et' = rotTrace (s.map k')

theorem KempeWitness.rot {s : List E} {k : E → Color} (h : H.KempeWitness s k) :
    H.RotKempeWitness s k := by
  obtain ⟨n, hn⟩ := exists_rotate_succ s
  obtain ⟨w, hw, hw'⟩ := h.rotate n
  rw [trace_map_of_rotate_one hn k] at hw
  refine ⟨w, hw, fun et' het' => ?_⟩
  obtain ⟨k', hk', hek⟩ := hw' et' het'
  exact ⟨k', hk', by rw [hek, trace_map_of_rotate_one hn k']⟩

/-- Conversely, a rotated-trace witness is a witness for a suitable rotation. -/
theorem RotKempeWitness.kempeWitness {s : List E} {k : E → Color}
    (h : H.RotKempeWitness s k) (n : ℕ) (hn : (s.rotate n).rotate 1 = s) :
    H.KempeWitness (s.rotate n) k := by
  obtain ⟨w, hw, hw'⟩ := h
  refine ⟨w, by rw [trace_map_of_rotate_one hn k]; exact hw, fun et' het' => ?_⟩
  obtain ⟨k', hk', hek⟩ := hw' et' het'
  exact ⟨k', hk', by rw [hek, trace_map_of_rotate_one hn k']⟩

end Hypermap

namespace Hypermap

section Contract

variable {D : Type*} [DecidableEq D] {G : Hypermap D} {z : D} {hez : G.edge z ≠ z}

/-! ### Helper lemmas for the induction step -/

omit [DecidableEq D] in
theorem face_edge_ne_z (hp : G.Plain) (hnid : ∀ x : D, G.node x ≠ x) :
    G.face (G.edge z) ≠ z := by
  intro hc
  have h := hp.node_face (G.edge z)
  rw [hc, hp.edge_edge] at h
  exact hnid z h

theorem contractExtend_eq_of_ne
    (k1 : Walkup (G.walkupN z) (contractDart G z hez) → Color) (c d c' d' : Color)
    {y : D} (h1 : y ≠ z) (h2 : y ≠ G.edge z) :
    contractExtend k1 c d y = contractExtend k1 c' d' y := by
  rw [contractExtend_of_ne h1 h2, contractExtend_of_ne h1 h2]

theorem contractExtend_face_ez (hfe : G.face (G.edge z) ≠ z)
    (k1 : Walkup (G.walkupN z) (contractDart G z hez) → Color) (c : Color) :
    contractExtend k1 c (contractExtend k1 0 0 (G.face (G.edge z))) (G.face (G.edge z))
      = contractExtend k1 0 0 (G.face (G.edge z)) := by
  by_cases hy : G.face (G.edge z) = G.edge z
  · rw [hy, contractExtend_ez]
  · exact contractExtend_eq_of_ne k1 _ _ _ _ hfe hy

/-- Along a `node` chain avoiding the two deleted darts, `adjNode` is `node`. -/
theorem isChain_adjNode : ∀ (l : List D),
    List.IsChain (fun a b => b = G.node a) l →
    (∀ x ∈ l, x ≠ z ∧ x ≠ G.edge z) →
    List.IsChain (fun a b => b = adjNode G z a) l := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hl havoid
    cases t with
    | nil => simp
    | cons b t' =>
      rw [List.isChain_cons_cons] at hl ⊢
      obtain ⟨hab, hrest⟩ := hl
      refine ⟨?_, ih hrest fun x hx => havoid x (List.mem_cons_of_mem _ hx)⟩
      have hb := havoid b (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [adjNode_eq_node (by rw [← hab]; exact hb.1) (by rw [← hab]; exact hb.2)]
      exact hab

end Contract

end Hypermap

theorem getLastD_eq_getLast {α : Type*} (l : List α) (h : l ≠ []) (d : α) :
    l.getLastD d = l.getLast h := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  rfl

theorem add_mid_cancel (x y w : Color) : x + y + (y + w) = x + w := by
  rw [add_assoc, ← add_assoc y y w, Color.add_self, zero_add]

theorem add_add_self_left (a b : Color) : a + (b + a) = b := by
  rw [add_comm b a, ← add_assoc, Color.add_self, zero_add]

theorem add_add_self_right (a b : Color) : b + a + a = b := by
  rw [add_assoc, Color.add_self, add_zero]

namespace Hypermap

section Ring

variable {D : Type*} [Finite D] [DecidableEq D] {G : Hypermap D} {z : D} {q : List D}

omit [Finite D] [DecidableEq D] in
theorem node_of_cyclicChain_cons {x y : D} {t : List D}
    (h : IsCyclicChain (fun a b => b = G.node a) (x :: y :: t)) : y = G.node x :=
  (List.isChain_cons_cons.mp h.isChain).1

omit [Finite D] [DecidableEq D] in
theorem node_getLastD_cyclicChain
    (h : IsCyclicChain (fun a b => b = G.node a) (z :: q)) :
    G.node (q.getLastD z) = z := by
  have h2 := ((isCyclicChain_cons.mp h).2).symm
  rwa [← getLastD_eq_getLast (z :: q) (List.cons_ne_nil z q) z,
    List.getLastD_cons] at h2

theorem adjNode_eq_node_of_not_mem {r : List D} (hp : G.Plain)
    (hcyc : IsCyclicChain (fun a b => b = G.node a) r) (hzr : z ∈ r)
    {y : D} (hy : y ∉ r) (hyf : y ≠ G.face z) : adjNode G z y = G.node y := by
  refine adjNode_eq_node ?_ ?_
  · intro hc
    exact hy ((node_mem_iff_mem hcyc y).mp (by rw [hc]; exact hzr))
  · intro hc
    exact hyf (G.node.injective (hc.trans (hp.node_face z).symm))

theorem adjNode_cubic {r : List D} (hp : G.Plain) (hcub : G.Quasicubic r)
    (hcyc : IsCyclicChain (fun a b => b = G.node a) r) (hzr : z ∈ r)
    {x : D} (hxr : x ∉ r) (h0 : x ≠ G.face z)
    (h1 : G.node x ≠ G.face z) (h2 : G.node (G.node x) ≠ G.face z) :
    adjNode G z (adjNode G z (adjNode G z x)) = x ∧ adjNode G z x ≠ x := by
  have hn1 : G.node x ∉ r := fun hc => hxr ((node_mem_iff_mem hcyc x).mp hc)
  have hn2 : G.node (G.node x) ∉ r := fun hc => hn1 ((node_mem_iff_mem hcyc _).mp hc)
  rw [adjNode_eq_node_of_not_mem hp hcyc hzr hxr h0,
    adjNode_eq_node_of_not_mem hp hcyc hzr hn1 h1,
    adjNode_eq_node_of_not_mem hp hcyc hzr hn2 h2]
  exact ⟨hcub.node_node_node hxr, hcub.node_ne hxr⟩

end Ring

section Contract

variable {D : Type*} [DecidableEq D] {G : Hypermap D} {z : D} {hez : G.edge z ≠ z}

/-- The lifted ring inherits the geometrical hypotheses. -/
theorem contract_geo [Fintype D] (hp : G.Plain) (hnid : ∀ x : D, G.node x ≠ x)
    (hplanar : G.Planar)
    {s : List (Walkup (G.walkupN z) (contractDart G z hez))} {q' : List D}
    (hs : s.map contractProj = q')
    (h1 : IsCyclicChain (fun a b => b = adjNode G z a) q')
    (h2 : q'.Nodup)
    (h3 : ∀ x : D, x ≠ z → x ≠ G.edge z → x ∉ q' →
      adjNode G z (adjNode G z (adjNode G z x)) = x ∧ adjNode G z x ≠ x) :
    (contract G z hez).UcyclePlanarPlainQuasicubic s := by
  have hmem : ∀ u, u ∉ s → contractProj u ∉ q' := by
    intro u hu hmem
    rw [← hs] at hmem
    obtain ⟨v, hv, hvu⟩ := List.mem_map.mp hmem
    exact hu (contractProj_injective hvu ▸ hv)
  refine ⟨⟨⟨contract_plain hp, ?_⟩, ?_, ?_⟩, contract_planar hplanar⟩
  · constructor
    · intro u hu
      refine contractProj_injective ?_
      rw [contractProj_adjNode hp hnid, contractProj_adjNode hp hnid,
        contractProj_adjNode hp hnid]
      exact (h3 _ (contractProj_ne_z u) (contractProj_ne_ez u) (hmem u hu)).1
    · intro u hu hcon
      refine (h3 _ (contractProj_ne_z u) (contractProj_ne_ez u) (hmem u hu)).2 ?_
      rw [← contractProj_adjNode hp hnid, hcon]
  · refine isCyclicChain_of_map (f := contractProj) ?_ (by rw [hs]; exact h1)
    intro u v huv
    exact contractProj_injective (huv.trans (contractProj_adjNode hp hnid u).symm)
  · exact List.Nodup.of_map contractProj (by rw [hs]; exact h2)

/-- Contraction removes exactly two darts. -/
theorem card_contract [Fintype D] :
    Nat.card D = Nat.card (Walkup (G.walkupN z) (contractDart G z hez)) + 2 := by
  have h1 : Nat.card D = Nat.card (Walkup G z) + 1 := card_walkup G z
  have h2 : Nat.card (Walkup G z) =
      Nat.card (Walkup (G.walkupN z) (contractDart G z hez)) + 1 :=
    card_walkup (G.walkupN z) (contractDart G z hez)
  omega

end Contract

end Hypermap

/-! ### Trace algebra for the induction step -/

theorem rotTrace_map_cons {α : Type*} (f : α → Color) (x : α) (l : List α) :
    rotTrace ((x :: l).map f) =
      (f (l.getLastD x) + f x) :: pairmap (· + ·) (f x) (l.map f) := by
  rw [List.map_cons, rotTrace, List.getLastD_cons, getLastD_map, pairmap_cons]

theorem rotTrace_map_cons_cons {α : Type*} (f : α → Color) (a b : α) (l : List α) :
    rotTrace ((a :: b :: l).map f) =
      (f (l.getLastD b) + f a) :: (f a + f b) :: pairmap (· + ·) (f b) (l.map f) := by
  rw [rotTrace_map_cons, List.getLastD_cons, List.map_cons, pairmap_cons]

theorem pairmap_eq_rotTrace {α : Type*} (f : α → Color) (a : α) (l : List α)
    (h : f (l.getLastD a) = f a) :
    pairmap (· + ·) (f a) (l.map f) = rotTrace (l.map f) := by
  cases l with
  | nil => rfl
  | cons y t =>
    rw [List.getLastD_cons] at h
    rw [List.map_cons, rotTrace, List.getLastD_cons, getLastD_map, h]

/-- The trace of a ring whose second dart closes the face of the first. -/
theorem rotTrace_map_cons_cons_eq {α : Type*} (f : α → Color) (x y : α) (l : List α)
    (h : f (l.getLastD y) = f y) :
    rotTrace ((x :: y :: l).map f) =
      (f y + f x) :: (f x + f y) :: rotTrace (l.map f) := by
  rw [rotTrace_map_cons_cons, h, pairmap_eq_rotTrace f y l h]

/-! ### The chromogram surgery of the induction step -/

private theorem addTbl11 : Color.c1 + Color.c1 = 0 := rfl
private theorem addTbl12 : Color.c1 + Color.c2 = Color.c3 := rfl
private theorem addTbl13 : Color.c1 + Color.c3 = Color.c2 := rfl
private theorem addTbl21 : Color.c2 + Color.c1 = Color.c3 := rfl
private theorem addTbl22 : Color.c2 + Color.c2 = 0 := rfl
private theorem addTbl23 : Color.c2 + Color.c3 = Color.c1 := rfl
private theorem addTbl31 : Color.c3 + Color.c1 = Color.c2 := rfl
private theorem addTbl32 : Color.c3 + Color.c2 = Color.c1 := rfl
private theorem addTbl33 : Color.c3 + Color.c3 = 0 := rfl

attribute [local simp] addTbl11 addTbl12 addTbl13 addTbl21 addTbl22 addTbl23
  addTbl31 addTbl32 addTbl33

/-- The chromogram surgery contracting the first two symbols into one, used in
the second case of the induction step. -/
def kempeRot (s1 s2 : GramSymbol) (w : Chromogram) : Chromogram :=
  if s1 = .skip ∨ s2 = .skip then .push :: gramNeg w
  else .skip :: (if s2 = .push then gramFlip w else w)

/-- The two-symbol prefixes that a chromogram matching a trace with distinct
first two colours can have. -/
def GoodPair (s1 s2 : GramSymbol) : Prop :=
  (s1 = .push ∧ s2 ≠ .pop0) ∨ (s1 = .skip ∧ s2 = .push)

theorem goodPair_of_matchg {a b : Color} (hne : a ≠ b) {R : List Color}
    {s1 s2 : GramSymbol} {w : Chromogram}
    (h : matchg [] (a :: b :: R) (s1 :: s2 :: w)) : GoodPair s1 s2 := by
  cases s1 <;> cases s2 <;> cases a <;> cases b <;> simp_all [GoodPair, matchStep]

/-- `kempeRot s1 s2 w` matches exactly the traces obtained from those matched by
`s1 :: s2 :: w` by merging their first two (distinct) colours. -/
theorem matchg_kempeRot_iff {s1 s2 : GramSymbol} (hg : GoodPair s1 s2) {w : Chromogram}
    {c : Color} {R : List Color} :
    matchg [] (c :: R) (kempeRot s1 s2 w) ↔
      ∃ a b : Color, a ≠ b ∧ a + b = c ∧ matchg [] (a :: b :: R) (s1 :: s2 :: w) := by
  rcases hg with ⟨rfl, hs2⟩ | ⟨rfl, rfl⟩
  · cases s2 with
    | pop0 => exact absurd rfl hs2
    | skip =>
      have hk : kempeRot GramSymbol.push GramSymbol.skip w = GramSymbol.push :: gramNeg w := by
        rw [kempeRot, ite_eq_left (Or.inr rfl)]
      rw [hk]
      constructor
      · intro h
        cases c with
        | c0 => simp [matchStep] at h
        | c1 => simp [matchStep] at h
        | c2 =>
          exact ⟨Color.c3, Color.c1, by decide, by decide, by
            simpa [matchStep, matchg_gramNeg] using h⟩
        | c3 =>
          exact ⟨Color.c2, Color.c1, by decide, by decide, by
            simpa [matchStep, matchg_gramNeg] using h⟩
      · rintro ⟨a, b, hab, rfl, h⟩
        cases a <;> cases b <;> simp_all [matchStep, matchg_gramNeg]
    | push =>
      have hk : kempeRot GramSymbol.push GramSymbol.push w
          = GramSymbol.skip :: gramFlip w := by
        rw [kempeRot, ite_eq_right (by simp)]
        simp
      rw [hk]
      constructor
      · intro h
        cases c with
        | c0 => simp [matchStep] at h
        | c2 => simp [matchStep] at h
        | c3 => simp [matchStep] at h
        | c1 =>
          rw [matchg_cons] at h
          simp only [matchStep, Option.elim, matchg_gramFlip, Bool.or_eq_true] at h
          rcases h with h | h
          · exact ⟨Color.c2, Color.c3, by decide, by decide, by simpa [matchStep] using h⟩
          · exact ⟨Color.c3, Color.c2, by decide, by decide, by simpa [matchStep] using h⟩
      · rintro ⟨a, b, hab, rfl, h⟩
        cases a <;> cases b <;>
          simp_all [matchStep, matchg_gramFlip]
    | pop1 =>
      have hk : kempeRot GramSymbol.push GramSymbol.pop1 w = GramSymbol.skip :: w := by
        rw [kempeRot, ite_eq_right (by simp)]
        simp
      rw [hk]
      constructor
      · intro h
        cases c with
        | c0 => simp [matchStep] at h
        | c2 => simp [matchStep] at h
        | c3 => simp [matchStep] at h
        | c1 =>
          exact ⟨Color.c2, Color.c3, by decide, by decide, by simpa [matchStep] using h⟩
      · rintro ⟨a, b, hab, rfl, h⟩
        cases a <;> cases b <;> simp_all [matchStep]
  · have hk : kempeRot GramSymbol.skip GramSymbol.push w = GramSymbol.push :: gramNeg w := by
      rw [kempeRot, ite_eq_left (Or.inl rfl)]
    rw [hk]
    constructor
    · intro h
      cases c with
      | c0 => simp [matchStep] at h
      | c1 => simp [matchStep] at h
      | c2 =>
        exact ⟨Color.c1, Color.c3, by decide, by decide, by
          simpa [matchStep, matchg_gramNeg] using h⟩
      | c3 =>
        exact ⟨Color.c1, Color.c2, by decide, by decide, by
          simpa [matchStep, matchg_gramNeg] using h⟩
    · rintro ⟨a, b, hab, rfl, h⟩
      cases a <;> cases b <;> simp_all [matchStep, matchg_gramNeg]

/-! ### The chromogram surgery of the degenerate case -/

/-- The chromogram surgery prefixing a doubled colour, used in the first case of
the induction step. -/
def kempeDup (e : Color) (w : Chromogram) : Chromogram :=
  if e = Color.c1 then .skip :: .skip :: w else .push :: .pop0 :: w

theorem matchg_kempeDup {e : Color} (he : e ≠ 0) (et : List Color) (w : Chromogram) :
    matchg [] (e :: e :: et) (kempeDup e w) = matchg [] et w := by
  cases e with
  | c0 => exact absurd rfl he
  | c1 => simp [kempeDup, matchStep]
  | c2 => simp [kempeDup, matchStep]
  | c3 => simp [kempeDup, matchStep]

theorem matchg_kempeDup_inv {e : Color} {et' : List Color} {w : Chromogram}
    (h : matchg [] et' (kempeDup e w)) :
    ∃ e2 et2, e2 ≠ 0 ∧ et' = e2 :: e2 :: et2 ∧ matchg [] et2 w := by
  by_cases he : e = Color.c1
  · rw [kempeDup, ite_eq_left he] at h
    match et' with
    | [] => simp at h
    | [c] => cases c <;> simp [matchStep] at h
    | a :: b :: et2 =>
      have ha : a = Color.c1 := by
        cases a <;> first | rfl | (exfalso; revert h; simp [matchStep])
      subst ha
      have hb : b = Color.c1 := by
        cases b <;> first | rfl | (exfalso; revert h; simp [matchStep])
      subst hb
      exact ⟨Color.c1, et2, by decide, rfl, by simpa [matchStep] using h⟩
  · rw [kempeDup, ite_eq_right he] at h
    match et' with
    | [] => simp at h
    | [c] => cases c <;> simp [matchStep] at h
    | a :: b :: et2 =>
      have hab : (a = Color.c2 ∧ b = Color.c2) ∨ (a = Color.c3 ∧ b = Color.c3) := by
        cases a <;> cases b <;>
          first
            | exact Or.inl ⟨rfl, rfl⟩
            | exact Or.inr ⟨rfl, rfl⟩
            | (exfalso; revert h; simp [matchStep])
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Color.c2, et2, by decide, rfl, by simpa [matchStep] using h⟩
      · exact ⟨Color.c3, et2, by decide, rfl, by simpa [matchStep] using h⟩

/-! ### The induction step -/

namespace Hypermap

universe u

open Color

private theorem kempeWitness_step {n : ℕ}
    (ih : ∀ (E : Type u) [Fintype E] [DecidableEq E] (H : Hypermap E) (t : List E),
      Nat.card E ≤ n → H.UcyclePlanarPlainQuasicubic t →
      ∀ k1 : E → Color, H.Coloring k1 → H.KempeWitness t k1)
    {D : Type u} [Fintype D] [DecidableEq D] {G : Hypermap D} {z : D} {q : List D}
    (hcard : Nat.card D ≤ n + 1)
    (geo : G.UcyclePlanarPlainQuasicubic (z :: q))
    {k : D → Color} (hk : G.Coloring k)
    (hfz : G.face z = z ∨ G.face z ∉ (z :: q)) :
    G.RotKempeWitness (z :: q) k := by
  have hp : G.Plain := geo.base.base.plain
  have hcub : G.Quasicubic (z :: q) := geo.base.base.quasicubic
  have hcyc : IsCyclicChain (fun a b => b = G.node a) (z :: q) := geo.base.cycle
  have hnd : (z :: q).Nodup := geo.base.nodup
  have hplanar : G.Planar := geo.planar
  have hnid : ∀ x : D, G.node x ≠ x := hk.node_ne
  have hez : G.edge z ≠ z := hp.edge_ne z
  have hzmem : z ∈ z :: q := List.mem_cons_self
  have hglast : G.node (q.getLastD z) = z := node_getLastD_cyclicChain hcyc
  have hlast : q.getLastD z = G.face (G.edge z) :=
    G.node.injective (hglast.trans (G.edgeK z).symm)
  have hqne : q ≠ [] := by
    rintro rfl
    exact hnid z (isCyclicChain_singleton.mp hcyc).symm
  obtain ⟨nz, q1, rfl⟩ : ∃ nz q1, q = nz :: q1 := by
    cases q with
    | nil => exact absurd rfl hqne
    | cons a t => exact ⟨a, t, rfl⟩
  have hnzdef : nz = G.node z := node_of_cyclicChain_cons hcyc
  have hkH : (contract G z hez).Coloring (k ∘ contractProj) := contract_coloring hp hnid hk
  have hcardH : Nat.card (Walkup (G.walkupN z) (contractDart G z hez)) ≤ n := by
    have h := card_contract (G := G) (z := z) (hez := hez)
    omega
  have hfe : G.face (G.edge z) ≠ z := face_edge_ne_z hp hnid
  rcases hfz with hfza | hfzb
  · -- Case (a): the face at `z` is degenerate, so `edge z = node z` is on the ring
    have hnzez : nz = G.edge z := by
      have h := hp.node_face z
      rw [hfza] at h
      rw [hnzdef]; exact h
    subst hnzez
    have hnd' : ((G.edge z) :: q1).Nodup := hnd.of_cons
    have hq1avoid : ∀ x ∈ q1, x ≠ z ∧ x ≠ G.edge z := by
      intro x hx
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hx)
      · rintro rfl
        exact (List.nodup_cons.mp hnd').1 hx
    have hlast1 : q1.getLastD (G.edge z) = G.face (G.edge z) := by
      rw [← hlast, List.getLastD_cons]
    have hq1cyc : IsCyclicChain (fun a b => b = adjNode G z a) q1 := by
      have hchain1 : List.IsChain (fun a b => b = G.node a) q1 :=
        (List.isChain_cons.mp (List.isChain_cons_cons.mp hcyc.isChain).2).2
      cases q1 with
      | nil => simp
      | cons c t =>
        rw [isCyclicChain_cons]
        refine ⟨isChain_adjNode _ hchain1 hq1avoid, ?_⟩
        have hgl : (c :: t).getLast (List.cons_ne_nil c t) = G.face (G.edge z) := by
          rw [← getLastD_eq_getLast (c :: t) (List.cons_ne_nil c t) (G.edge z)]
          exact hlast1
        rw [hgl, adjNode_of_node_eq_z (G.edgeK z)]
        exact (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hcyc.isChain).2).1
    have hq1cub : ∀ x : D, x ≠ z → x ≠ G.edge z → x ∉ q1 →
        adjNode G z (adjNode G z (adjNode G z x)) = x ∧ adjNode G z x ≠ x := by
      intro x hx1 hx2 hx3
      have hxr : x ∉ z :: G.edge z :: q1 := by
        intro hc
        rcases List.mem_cons.mp hc with h | h
        · exact hx1 h
        · rcases List.mem_cons.mp h with h | h
          · exact hx2 h
          · exact hx3 h
      have hnr : ∀ y : D, y ∉ z :: G.edge z :: q1 → G.node y ∉ z :: G.edge z :: q1 :=
        fun y hy hc => hy ((node_mem_iff_mem hcyc y).mp hc)
      refine adjNode_cubic hp hcub hcyc hzmem hxr ?_ ?_ ?_
      · rw [hfza]; exact hx1
      · rw [hfza]
        intro hc
        exact hnr x hxr (by rw [hc]; exact hzmem)
      · rw [hfza]
        intro hc
        exact hnr _ (hnr x hxr) (by rw [hc]; exact hzmem)
    obtain ⟨s, hs⟩ := exists_lift_list (hez := hez) q1 hq1avoid
    have hgeoH : (contract G z hez).UcyclePlanarPlainQuasicubic s :=
      contract_geo hp hnid hplanar hs hq1cyc ((List.nodup_cons.mp hnd').2) hq1cub
    have htrace : ∀ k0 : D → Color, k0 (G.face (G.edge z)) = k0 (G.edge z) →
        rotTrace ((z :: G.edge z :: q1).map k0)
          = (k0 (G.edge z) + k0 z) :: (k0 z + k0 (G.edge z)) :: rotTrace (q1.map k0) := by
      intro k0 hk0
      refine rotTrace_map_cons_cons_eq k0 z (G.edge z) q1 ?_
      rw [hlast1]; exact hk0
    obtain ⟨w, hw, hw'⟩ := (ih _ (contract G z hez) s hcardH hgeoH _ hkH).rot
    rw [show s.map (k ∘ contractProj) = q1.map k by rw [← List.map_map, hs]] at hw
    have he1 : k (G.edge z) + k z ≠ 0 := fun h => hk.edge z (Color.add_eq_zero_iff.mp h)
    refine ⟨kempeDup (k (G.edge z) + k z) w, ?_, ?_⟩
    · rw [htrace k (hk.face _), show k z + k (G.edge z) = k (G.edge z) + k z from add_comm _ _,
        matchg_kempeDup he1]
      exact hw
    · intro et' het'
      obtain ⟨e2, et2, he2, rfl, hmatch⟩ := matchg_kempeDup_inv het'
      obtain ⟨k1, hk1, het2⟩ := hw' et2 hmatch
      have hk0 : G.Coloring
          (contractExtend k1 (e2 + contractExtend k1 0 0 (G.face (G.edge z)))
            (contractExtend k1 0 0 (G.face (G.edge z)))) := by
        refine contract_coloring_lift hp hnid hk1 ?_ ?_ ?_
        · intro hc
          exact he2 (by simpa using hc)
        · rw [hfza]; exact contractExtend_z
        · exact contractExtend_face_ez hfe k1 _
      refine ⟨_, hk0, ?_⟩
      have hq10 : q1.map (contractExtend k1 (e2 + contractExtend k1 0 0 (G.face (G.edge z)))
          (contractExtend k1 0 0 (G.face (G.edge z)))) = s.map k1 := by
        rw [← hs, List.map_map]
        exact List.map_congr_left fun u _ => contractExtend_contractProj u
      rw [htrace _ (contractExtend_face_ez hfe k1 _ |>.trans contractExtend_ez.symm),
        contractExtend_z, contractExtend_ez, hq10, ← het2]
      have h1 : contractExtend k1 0 0 (G.face (G.edge z))
          + (e2 + contractExtend k1 0 0 (G.face (G.edge z))) = e2 :=
        add_add_self_left _ _
      have h2 : e2 + contractExtend k1 0 0 (G.face (G.edge z))
          + contractExtend k1 0 0 (G.face (G.edge z)) = e2 := add_add_self_right _ _
      rw [h1, h2]
  · -- Case (b): the face at `z` leaves the ring
    have hfzz : G.face z ≠ z := fun hc => hfzb (by rw [hc]; exact hzmem)
    have hfzez : G.face z ≠ G.edge z := by
      intro hc
      have h := hp.node_face z
      rw [hc] at h
      exact hnid (G.edge z) h
    have hezr : G.edge z ∉ z :: nz :: q1 := by
      intro hc
      exact hfzb ((node_mem_iff_mem hcyc (G.face z)).mp (by rw [hp.node_face z]; exact hc))
    have hnezr : G.node (G.edge z) ∉ z :: nz :: q1 := fun hc =>
      hezr ((node_mem_iff_mem hcyc (G.edge z)).mp hc)
    have hnezz : G.node (G.edge z) ≠ z := fun hc => hnezr (by rw [hc]; exact hzmem)
    have hnezez : G.node (G.edge z) ≠ G.edge z := hnid (G.edge z)
    have hnodenez : G.node (G.node (G.edge z)) = G.face z := by
      have h := hcub.node_node_node hfzb
      rw [hp.node_face z] at h
      exact h
    have hfznez : G.face z ≠ G.node (G.edge z) := by
      intro hc
      rw [← hc] at hnodenez
      exact hnid _ hnodenez
    have hq'avoid : ∀ x ∈ (G.node (G.edge z) :: G.face z :: nz :: q1),
        x ≠ z ∧ x ≠ G.edge z := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact ⟨hnezz, hnezez⟩
      · rcases List.mem_cons.mp h with h2 | h2
        · rw [h2]; exact ⟨hfzz, hfzez⟩
        · refine ⟨fun hc => ?_, fun hc => ?_⟩
          · apply (List.nodup_cons.mp hnd).1
            rw [← hc]; exact h2
          · apply hezr
            rw [← hc]; exact List.mem_cons_of_mem _ h2
    have hq'nodup : (G.node (G.edge z) :: G.face z :: nz :: q1).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, (List.nodup_cons.mp hnd).2⟩⟩
      · intro hc
        rcases List.mem_cons.mp hc with heq | hc2
        · exact hfznez heq.symm
        · exact hnezr (List.mem_cons_of_mem _ hc2)
      · exact fun hc => hfzb (List.mem_cons_of_mem _ hc)
    have hq'cyc : IsCyclicChain (fun a b => b = adjNode G z a)
        (G.node (G.edge z) :: G.face z :: nz :: q1) := by
      rw [isCyclicChain_cons]
      refine ⟨?_, ?_⟩
      · rw [List.isChain_cons_cons]
        refine ⟨?_, ?_⟩
        · rw [adjNode_eq_node (by rw [hnodenez]; exact hfzz) (by rw [hnodenez]; exact hfzez),
            hnodenez]
        · rw [List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · rw [adjNode_of_node_eq_ez (by rw [hp.node_face z]; exact hez) (hp.node_face z)]
            exact hnzdef
          · exact isChain_adjNode _ (List.isChain_cons_cons.mp hcyc.isChain).2
              fun x hx => hq'avoid x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      · have hgl : (G.node (G.edge z) :: G.face z :: nz :: q1).getLast (by simp)
            = G.face (G.edge z) := by
          rw [← getLastD_eq_getLast _ _ z, List.getLastD_cons, List.getLastD_cons]
          exact hlast
        rw [hgl, adjNode_of_node_eq_z (G.edgeK z)]
    have hq'cub : ∀ x : D, x ≠ z → x ≠ G.edge z →
        x ∉ (G.node (G.edge z) :: G.face z :: nz :: q1) →
        adjNode G z (adjNode G z (adjNode G z x)) = x ∧ adjNode G z x ≠ x := by
      intro x hx1 hx2 hx3
      have hxnez : x ≠ G.node (G.edge z) := fun hc => hx3 (by rw [hc]; exact List.mem_cons_self)
      have hxfz : x ≠ G.face z := fun hc =>
        hx3 (by rw [hc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hxq : x ∉ nz :: q1 := fun hc =>
        hx3 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
      have hxr : x ∉ z :: nz :: q1 := by
        intro hc
        rcases List.mem_cons.mp hc with heq | hc2
        · exact hx1 heq
        · exact hxq hc2
      refine adjNode_cubic hp hcub hcyc hzmem hxr hxfz ?_ ?_
      · intro hc
        exact hxnez (G.node.injective (hc.trans hnodenez.symm))
      · intro hc
        exact hx2 (G.node.injective (G.node.injective (hc.trans hnodenez.symm)))
    obtain ⟨s, hs⟩ := exists_lift_list (hez := hez)
      (G.node (G.edge z) :: G.face z :: nz :: q1) hq'avoid
    have hgeoH : (contract G z hez).UcyclePlanarPlainQuasicubic s :=
      contract_geo hp hnid hplanar hs hq'cyc hq'nodup hq'cub
    have htraceOld : ∀ k0 : D → Color, k0 (G.face (G.edge z)) = k0 (G.edge z) →
        rotTrace ((z :: nz :: q1).map k0)
          = (k0 (G.edge z) + k0 z) :: pairmap (· + ·) (k0 z) ((nz :: q1).map k0) := by
      intro k0 h
      rw [rotTrace_map_cons, hlast, h]
    have htraceNew : ∀ k0 : D → Color, k0 (G.face (G.edge z)) = k0 (G.edge z) →
        rotTrace ((G.node (G.edge z) :: G.face z :: nz :: q1).map k0)
          = (k0 (G.edge z) + k0 (G.node (G.edge z)))
            :: (k0 (G.node (G.edge z)) + k0 (G.face z))
            :: pairmap (· + ·) (k0 (G.face z)) ((nz :: q1).map k0) := by
      intro k0 h
      rw [rotTrace_map_cons_cons, List.getLastD_cons, ← List.getLastD_cons (a := z), hlast, h]
    obtain ⟨w, hw, hw'⟩ := (ih _ (contract G z hez) s hcardH hgeoH _ hkH).rot
    rw [show s.map (k ∘ contractProj) = (G.node (G.edge z) :: G.face z :: nz :: q1).map k by
      rw [← List.map_map, hs], htraceNew k (hk.face _), hk.face z] at hw
    have hab : k (G.edge z) + k (G.node (G.edge z))
        ≠ k (G.node (G.edge z)) + k z := by
      intro hc
      refine hk.edge z (Color.add_eq_zero_iff.mp ?_)
      rw [← add_mid_cancel (k (G.edge z)) (k (G.node (G.edge z))) (k z)]
      exact Color.add_eq_zero_iff.mpr hc
    obtain ⟨s1, s2, w', rfl⟩ : ∃ s1 s2 w', w = s1 :: s2 :: w' := by
      have hlen := matchg_length _ _ _ hw
      match w with
      | [] => simp at hlen
      | [_] => simp at hlen
      | a :: b :: t => exact ⟨a, b, t, rfl⟩
    have hg : GoodPair s1 s2 := goodPair_of_matchg hab hw
    refine ⟨kempeRot s1 s2 w', ?_, ?_⟩
    · rw [htraceOld k (hk.face _)]
      exact (matchg_kempeRot_iff hg).mpr ⟨_, _, hab, add_mid_cancel _ _ _, hw⟩
    · intro et' het'
      obtain ⟨e, et, rfl⟩ : ∃ e et, et' = e :: et := by
        match et' with
        | [] =>
          exfalso
          rw [kempeRot] at het'
          split at het' <;> simp at het'
        | e :: et => exact ⟨e, et, rfl⟩
      have he0 : e ≠ 0 := fun hc =>
        matchg_notMem_zero _ _ _ het' (by rw [← hc]; exact List.mem_cons_self)
      obtain ⟨a0, b0, hab0, hsum, hmatch⟩ := (matchg_kempeRot_iff hg).mp het'
      obtain ⟨k1, hk1, hk1trace⟩ := hw' _ hmatch
      have hk0fz : contractExtend k1 (contractExtend k1 0 0 (G.face z))
          (contractExtend k1 0 0 (G.face (G.edge z))) (G.face z)
          = contractExtend k1 0 0 (G.face z) :=
        contractExtend_eq_of_ne k1 _ _ _ _ hfzz hfzez
      have hk0fe : contractExtend k1 (contractExtend k1 0 0 (G.face z))
          (contractExtend k1 0 0 (G.face (G.edge z))) (G.face (G.edge z))
          = contractExtend k1 0 0 (G.face (G.edge z)) :=
        contractExtend_face_ez hfe k1 _
      have hmapk : (G.node (G.edge z) :: G.face z :: nz :: q1).map
          (contractExtend k1 (contractExtend k1 0 0 (G.face z))
            (contractExtend k1 0 0 (G.face (G.edge z)))) = s.map k1 := by
        rw [← hs, List.map_map]
        exact List.map_congr_left fun u _ => contractExtend_contractProj u
      rw [← hmapk, htraceNew _ (hk0fe.trans contractExtend_ez.symm), hk0fz,
        contractExtend_ez] at hk1trace
      simp only [List.cons.injEq] at hk1trace
      obtain ⟨ha0, hb0, het⟩ := hk1trace
      have hsum2 : contractExtend k1 0 0 (G.face z)
          + contractExtend k1 0 0 (G.face (G.edge z)) = e := by
        rw [← hsum, ha0, hb0, add_mid_cancel, add_comm]
      have hne : contractExtend k1 0 0 (G.face z)
          ≠ contractExtend k1 0 0 (G.face (G.edge z)) := by
        intro hc
        exact he0 (by rw [← hsum2, hc, Color.add_self])
      have hk0col : G.Coloring (contractExtend k1 (contractExtend k1 0 0 (G.face z))
          (contractExtend k1 0 0 (G.face (G.edge z)))) :=
        contract_coloring_lift hp hnid hk1 hne hk0fz hk0fe
      refine ⟨_, hk0col, ?_⟩
      rw [htraceOld _ (hk0fe.trans contractExtend_ez.symm), contractExtend_ez,
        contractExtend_z, het]
      rw [← hsum2, add_comm]

/-- The Kempe closure property, by induction on the number of darts. -/
theorem kempeWitness_of_card_le : ∀ (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D]
    (G : Hypermap D) (r : List D), Nat.card D ≤ n →
    G.UcyclePlanarPlainQuasicubic r → ∀ k : D → Color, G.Coloring k → G.KempeWitness r k := by
  intro n
  induction n with
  | zero =>
    intro D _ _ G r hcard _ k hk
    have hc0 : Fintype.card D = 0 := by rw [← Nat.card_eq_fintype_card]; omega
    have hem : IsEmpty D := Fintype.card_eq_zero_iff.mp hc0
    obtain rfl : r = [] := List.eq_nil_iff_forall_not_mem.mpr fun a _ => hem.elim a
    exact kempeWitness_nil hk
  | succ n ih =>
    intro D _ _ G r hcard geo k hk
    match r with
    | [] => exact kempeWitness_nil hk
    | x :: t =>
      obtain ⟨z, hzr, hzf⟩ := exists_ring_dart geo.planar geo.base.base.plain geo.base.cycle
        (List.mem_cons_self (a := x) (l := t))
      refine KempeWitness.of_normalised hzr ?_
      intro i p hip
      refine KempeWitness.of_rotate 1 ?_
      rw [hip]
      have geo' : G.UcyclePlanarPlainQuasicubic (z :: p) := hip ▸ (geo.rotate i).rotate 1
      have hzf' : G.face z = z ∨ G.face z ∉ (z :: p) := by
        rcases hzf with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          rw [← hip]
          simpa only [List.mem_rotate] using h
      obtain ⟨m, hm⟩ := exists_rotate_succ (z :: p)
      exact ((kempeWitness_step ih hcard geo' hk hzf').kempeWitness m hm).of_rotate m

/-- **Kempe closure of ring traces.**  The set of ring traces of a ring `r` of a
planar plain quasicubic hypermap whose ring is a duplicate-free node cycle is
Kempe-closed.  This is the reference's `Kempe_map`. -/
theorem Kempe_map {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D) (r : List D)
    (geo : G.UcyclePlanarPlainQuasicubic r) : KempeClosed (G.RingTrace r) :=
  kempeClosed_ringTrace_of_witness G r fun k hk =>
    kempeWitness_of_card_le (Nat.card D) D G r le_rfl geo k hk

end Hypermap

end FourColor

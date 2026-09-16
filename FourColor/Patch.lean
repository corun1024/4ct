import FourColor.Geometry
import FourColor.Coloring

/-!
# Patching two hypermaps along a ring

A hypermap `G` is *patched* from a "disk" map `Gd` and a "remainder" map `Gr`
when the two are glued along a common border: `hd` and `hr` embed the darts of
`Gd` and of `Gr` in `G`, their images cover `G` and meet exactly in the border
ring, and away from the border `hd` preserves E-links while `hr` preserves
N-links.  The relation is used in both directions: to build a new map by
glueing, and to cut a map along a ring.

The two sides are not symmetric.  The border of the disk is an E-cycle of `Gd`,
which must be face-simple; the border of the remainder is an N-cycle of `Gr`,
which need only be duplicate-free.  The two border lists traverse the ring in
opposite directions, which is what `Patch.ring` records.

## Main definitions

* `Patch` — the patch relation between `G`, `Gd` and `Gr`.
* `Hypermap.PlainOn` — plainness relative to a set of darts, the edge analogue
  of `Hypermap.CubicOn`.
* `Patch.Outer` — the darts of `G` whose face meets the remainder map.
* `gcomp`, `gcompDisk`, `gcompRem` — the component of a dart, and the two
  hypermaps it cuts `G` into.

## Main results

* `Patch.card_patch` — the two parts cover `G`, overlapping on the ring.
* `Patch.hd_edge_eq_hr_iff` — crossing the ring by an E-link of the disk is
  crossing it by an N-link of the remainder.
* `Patch.plain_patch`, `Patch.cubic_patch` — plainness and cubicity transfer.
* `Patch.cface_hd`, `Patch.cface_hd_iff`, `Patch.cface_hr_iff` — how the two
  embeddings interact with faces.
* `Patch.bridgeless`, `Patch.bridgeless_patch` — bridgelessness transfers, in
  both directions.
* `Patch.colorable_patch` — `G` is four-colourable exactly when the two parts
  admit colourings with matching ring traces.
* `Patch.genus_patch`, `Patch.planar_patch` — the genus of `G` is the sum of
  the genera of its parts, so `G` is planar exactly when both parts are.
* `Patch.connected_r` — the remainder of a connected map is connected.
* `patch_gcomp` — a hypermap is patched from any of its components and the
  complement of that component, along empty rings.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file
corresponds to `theories/proof/patch.v` of the Coq development.
-/

namespace FourColor

open Equiv Equiv.Perm

variable {D Dd Dr : Type*}

/-! ### Auxiliary facts about cyclic chains

A duplicate-free cyclic chain for `fun u v => v = f u` lists one orbit of `f`,
and its cyclic successor function *is* `f`.  Both facts are needed for the two
border rings. -/

/-- The darts of an `f`-cycle through `x` are exactly the darts of the orbit
of `x`.  This is the generic form of `Hypermap.cnode_iff_mem`. -/
private theorem sameCycle_iff_mem [Finite D] {f : Perm D} {r : List D}
    (hcyc : IsCyclicChain (fun u v => v = f u) r) {x : D} (hx : x ∈ r) (y : D) :
    f.SameCycle x y ↔ y ∈ r := by
  constructor
  · intro hxy
    have hxy' : Relation.ReflTransGen (fun a b => b = f a) x y :=
      (sameCycle_iff_reflTransGen f x y).mp hxy
    clear hxy
    induction hxy' with
    | refl => exact hx
    | tail _ hbc ih =>
      rw [hbc]
      exact mem_of_isCyclicChain hcyc ih
  · intro hy
    exact sameCycle_of_mem_isChain hcyc.isChain hx hy

/-- The darts of an `f`-cycle are closed under `f` and under its inverse. -/
private theorem mem_iff_apply_mem [Finite D] {f : Perm D} {r : List D}
    (hcyc : IsCyclicChain (fun u v => v = f u) r) (x : D) : f x ∈ r ↔ x ∈ r := by
  constructor
  · intro h
    exact (sameCycle_iff_mem hcyc h x).mp (sameCycle_apply_left.mpr (SameCycle.refl _ _))
  · intro h
    exact mem_of_isCyclicChain hcyc h

/-- In a cyclic chain for `fun u v => v = f u`, the dart at the cyclically next
position is the image of the dart at the current one. -/
private theorem getElem_succ {f : D → D} {r : List D}
    (hcyc : IsCyclicChain (fun u v => v = f u) r) {i k : ℕ} {hi : i < r.length}
    {hk : k < r.length} (hik : k = (i + 1) % r.length) : r[k] = f r[i] := by
  rcases Nat.lt_or_ge (i + 1) r.length with hlt | hge
  · have hk' : k = i + 1 := by rw [hik, Nat.mod_eq_of_lt hlt]
    subst hk'
    exact hcyc.isChain.getElem i hlt
  · have hi1 : i + 1 = r.length := by omega
    have hi' : r.length - 1 = i := by omega
    have hk0 : k = 0 := by rw [hik, hi1, Nat.mod_self]
    subst hk0
    have hmem1 : r[i] ∈ r.getLast? := by
      rw [Option.mem_def, List.getLast?_eq_getElem?, hi', List.getElem?_eq_getElem hi]
    have hmem2 : r[0] ∈ r.head? := by
      rw [Option.mem_def, List.head?_eq_getElem?, List.getElem?_eq_getElem]
    exact hcyc.2 _ hmem1 _ hmem2

/-- In a cyclic chain for `fun u v => v = f u` the cyclic successor is `f`. -/
private theorem cyclicNext_eq {f : D → D} {r : List D}
    (hcyc : IsCyclicChain (fun u v => v = f u) r) {x y : D} (h : CyclicNext r x y) :
    y = f x := by
  obtain ⟨n, t, hrot, rfl⟩ := h
  have hc : IsCyclicChain (fun u v => v = f u) (x :: t) := by
    rw [← hrot]
    exact isCyclicChain_rotate.mpr hcyc
  match t with
  | [] => simpa using isCyclicChain_singleton.mp hc
  | z :: t' => simpa using (List.isChain_cons_cons.mp hc.isChain).1

/-- The arithmetic behind the ring correspondence: walking one step forward
along the disk border is walking one step backward along the remainder
border. -/
private theorem cyclic_index_iff {n i j k l : ℕ} (hi : i < n) (hj : j < n)
    (hk : k = (i + 1) % n) (hl : l = (j + 1) % n) : n - 1 - k = j ↔ n - 1 - i = l := by
  subst hk; subst hl
  rcases Nat.lt_or_ge (i + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    rcases Nat.lt_or_ge (j + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2]; omega
    · have h3 : j + 1 = n := by omega
      rw [h3, Nat.mod_self]; omega
  · have h4 : i + 1 = n := by omega
    rw [h4, Nat.mod_self]
    rcases Nat.lt_or_ge (j + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2]; omega
    · have h3 : j + 1 = n := by omega
      rw [h3, Nat.mod_self]; omega

/-- Iterating `face` stays inside a face orbit. -/
private theorem cface_iterate (H : Hypermap D) (n : ℕ) (x : D) : H.CFace x (H.face^[n] x) :=
  ⟨(n : ℤ), by rw [zpow_natCast, Perm.coe_pow]⟩

/-- A map colouring is constant on each face orbit. -/
private theorem coloring_cface [Finite D] {G : Hypermap D} {k : D → Color}
    (hk : G.Coloring k) {x y : D} (h : G.CFace x y) : k x = k y := by
  have key : ∀ n : ℕ, k x = k (G.face^[n] x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply' G.face n x, hk.face, ih]
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Perm.coe_pow] at hn
  rw [← hn]
  exact key n

/-- Shifting the seed of a scan shifts every value. -/
private theorem scanl_add_const (c c₀ : Color) (l : List Color) :
    List.scanl (· + ·) (c + c₀) l = (List.scanl (· + ·) c₀ l).map (c + ·) := by
  induction l generalizing c₀ with
  | nil => rfl
  | cons x l ih => rw [List.scanl_cons, List.scanl_cons, List.map_cons, add_assoc, ih]

/-- Shifting the seed of `untrace` shifts the whole colouring. -/
private theorem untrace_add (c c₀ : Color) (et : List Color) :
    untrace (c + c₀) et = (untrace c₀ et).map (c + ·) := by
  match et with
  | [] => rfl
  | e :: t =>
    have h1 : untrace (c + c₀) (e :: t) = List.scanl (· + ·) (c + c₀) (e :: t).dropLast := rfl
    have h2 : untrace c₀ (e :: t) = List.scanl (· + ·) c₀ (e :: t).dropLast := rfl
    rw [h1, h2, scanl_add_const]

/-- Two colourings of a ring with the same trace differ by a constant. -/
private theorem eq_map_add_of_trace_eq : ∀ {A B : List Color}, A.length = B.length →
    trace A = trace B → B = A.map ((A.headD 0 + B.headD 0) + ·)
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | a :: A', b :: B', _, h => by
    simp only [List.headD_cons]
    have hab : a + b + a = b := by
      rw [add_right_comm, Color.add_self, zero_add]
    calc b :: B' = untrace b (trace (b :: B')) := (untrace_trace b B').symm
      _ = untrace (a + b + a) (trace (a :: A')) := by rw [hab, h]
      _ = (untrace a (trace (a :: A'))).map ((a + b) + ·) := untrace_add _ _ _
      _ = (a :: A').map ((a + b) + ·) := by rw [untrace_trace]

/-! ### Counting orbits and components

Every count below is the cardinality of a quotient, so the two tools needed are
a way to split a quotient by a predicate and a way to transport a quotient
along a partial correspondence. -/

/-- Iterating a permutation stays inside an orbit. -/
private theorem sameCycle_iterate {A : Type*} (f : Perm A) (n : ℕ) (x : A) :
    f.SameCycle x (f^[n] x) := ⟨(n : ℤ), by rw [zpow_natCast, Perm.coe_pow]⟩

/-- A list closed under `f` is closed under its iterates. -/
private theorem iterate_mem_iff {A : Type*} {f : Perm A} {l : List A}
    (h : ∀ x, f x ∈ l ↔ x ∈ l) (n : ℕ) (x : A) : f^[n] x ∈ l ↔ x ∈ l := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', h, ih]

/-- A list closed under `f` is closed along whole orbits. -/
private theorem sameCycle_iff_mem_aux {A : Type*} [Finite A] {f : Perm A} {l : List A}
    (h : ∀ x, f x ∈ l ↔ x ∈ l) {x y : A} (hxy : f.SameCycle x y) (hx : x ∈ l) : y ∈ l := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  rw [Perm.coe_pow] at hn
  rw [← hn]
  exact (iterate_mem_iff h n x).mpr hx

/-- The classes of `s` meeting `p`. -/
private def Meets {A : Type*} (s : Setoid A) (p : A → Prop) (q : Quotient s) : Prop :=
  ∃ x, Quotient.mk s x = q ∧ p x

/-- Splitting a finite type by a predicate. -/
private theorem card_split {X : Type*} [Finite X] (P : X → Prop) :
    Nat.card X = Nat.card {x // P x} + Nat.card {x // ¬ P x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl P).symm

/-- A trivially restricted subtype. -/
private theorem card_subtype_true {X : Type*} : Nat.card {_x : X // True} = Nat.card X :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)

/-- Transporting a quotient along a partial correspondence: `ι` need only be
defined on `A`, and its image need only meet every class satisfying `Q`. -/
private theorem card_quotient_eq {A B : Type*} {s : Setoid A} {t : Setoid B} (ι : A → B)
    (P : Quotient s → Prop) (Q : Quotient t → Prop)
    (hwd : ∀ x y : A, s.r x y ↔ t.r (ι x) (ι y))
    (hPQ : ∀ x : A, P (Quotient.mk s x) ↔ Q (Quotient.mk t (ι x)))
    (hsurj : ∀ q, Q q → ∃ x : A, Quotient.mk t (ι x) = q) :
    Nat.card {p : Quotient s // P p} = Nat.card {q : Quotient t // Q q} := by
  have hmap : ∀ x y : A, x ≈ y → ι x ≈ ι y := fun x y h => (hwd x y).mp h
  refine Nat.card_congr (Equiv.ofBijective
    (fun u => ⟨Quotient.map ι hmap u.1, ?_⟩) ⟨?_, ?_⟩)
  · induction u with | mk p hp => ?_
    revert hp
    refine Quotient.inductionOn p ?_
    intro x hx
    exact (hPQ x).mp hx
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ heq
    have heq' : Quotient.map ι hmap p = Quotient.map ι hmap p' := congrArg Subtype.val heq
    refine Subtype.ext ?_
    change p = p'
    clear heq
    clear hp hp'
    revert heq'
    refine Quotient.inductionOn₂ p p' ?_
    intro x y h
    exact Quotient.sound ((hwd x y).mpr (Quotient.exact h))
  · rintro ⟨q, hq⟩
    obtain ⟨x, hx⟩ := hsurj q hq
    refine ⟨⟨Quotient.mk s x, (hPQ x).mpr (by rw [hx]; exact hq)⟩, Subtype.ext ?_⟩
    exact hx

/-- A predicate satisfied by nothing meets no class. -/
private theorem card_meets_eq_zero {A : Type*} {s : Setoid A} {p : A → Prop}
    (hp : ∀ x, ¬ p x) : Nat.card {q : Quotient s // Meets s p q} = 0 := by
  have : IsEmpty {q : Quotient s // Meets s p q} :=
    ⟨fun u => by obtain ⟨x, -, hx⟩ := u.2; exact hp x hx⟩
  exact Nat.card_of_isEmpty

/-- A predicate contained in a single class meets exactly one class. -/
private theorem card_meets_eq_one {A : Type*} {s : Setoid A} {p : A → Prop} {x₀ : A}
    (hx₀ : p x₀) (hall : ∀ x, p x → s.r x₀ x) :
    Nat.card {q : Quotient s // Meets s p q} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨?_⟩, ⟨⟨Quotient.mk s x₀, ⟨x₀, rfl, hx₀⟩⟩⟩⟩
  rintro ⟨q, x, rfl, hx⟩ ⟨q', y, rfl, hy⟩
  exact Subtype.ext (Quotient.sound (s.trans (s.symm (hall x hx)) (hall y hy)))

/-- The darts of a duplicate-free list, counted. -/
private theorem card_mem_list {A : Type*} {l : List A} (h : l.Nodup) :
    Nat.card {x : A // x ∈ l} = l.length := by
  classical
  have hrw : Nat.card {x : A // x ∈ l} = Nat.card {x : A // x ∈ l.toFinset} := by
    simp only [List.mem_toFinset]
  rw [hrw, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

/-- **Orbit count of a patched permutation.**  If `fG` is covered by the images
of `f` and `g` under injections `a`, `b` which are morphisms — `b` everywhere,
`a` away from a list `l` that is a single `f`-orbit glued into the image of
`b` — then the orbits of `f` and `g` together are the orbits of `fG` plus the
glued one. -/
private theorem cycleCount_pair {A B C : Type*} [Finite A] [Finite B] [Finite C]
    {f : Perm A} {g : Perm B} {fG : Perm C} {a : A → C} {b : B → C} {l : List A}
    (hinja : Function.Injective a) (hinjb : Function.Injective b)
    (hb : ∀ y, b (g y) = fG (b y)) (ha : ∀ x ∉ l, a (f x) = fG (a x))
    (hl : ∀ x, f x ∈ l ↔ x ∈ l)
    (hcover : ∀ z : C, z ∉ Set.range b → z ∈ Set.range a)
    (hmem : ∀ x : A, a x ∈ Set.range b ↔ x ∈ l)
    (hcycle : ∀ x ∈ l, ∀ y ∈ l, f.SameCycle x y) :
    cycleCount f + cycleCount g = cycleCount fG + min l.length 1 := by
  classical
  -- the image of `b` is invariant
  have hinvb : ∀ z : C, z ∈ Set.range b ↔ fG z ∈ Set.range b := by
    intro z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨g y, hb y⟩
    · rintro ⟨y, hy⟩
      refine ⟨g⁻¹ y, fG.injective ?_⟩
      have h := hb (g⁻¹ y)
      rw [show g (g⁻¹ y) = y by simp] at h
      rw [← h, hy]
  have hinvb' : ∀ {z z' : C}, fG.SameCycle z z' → (z ∈ Set.range b ↔ z' ∈ Set.range b) := by
    intro z z' h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [Perm.coe_pow] at hn
    rw [← hn]
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply' fG n z, ← hinvb]; exact ih
  -- transport of orbits
  have hiterb : ∀ (n : ℕ) (y : B), b (g^[n] y) = fG^[n] (b y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply' g n y, hb, ih, Function.iterate_succ_apply']
  have hitera : ∀ (n : ℕ) (x : A), x ∉ l → a (f^[n] x) = fG^[n] (a x) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have hnb : f^[n] x ∉ l := fun hm => hx ((iterate_mem_iff hl n x).mp hm)
      rw [Function.iterate_succ_apply' f n x, ha _ hnb, ih x hx, Function.iterate_succ_apply']
  have hcycb : ∀ y y' : B, g.SameCycle y y' ↔ fG.SameCycle (b y) (b y') := by
    intro y y'
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [Perm.coe_pow] at hn
      rw [← hn, hiterb]
      exact sameCycle_iterate fG n (b y)
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [Perm.coe_pow, ← hiterb] at hn
      rw [← hinjb hn]
      exact sameCycle_iterate g n y
  have hcyca : ∀ (x x' : A), x ∉ l → (f.SameCycle x x' ↔ fG.SameCycle (a x) (a x')) := by
    intro x x' hx
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [Perm.coe_pow] at hn
      rw [← hn, hitera n x hx]
      exact sameCycle_iterate fG n (a x)
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [Perm.coe_pow, ← hitera n x hx] at hn
      rw [← hinja hn]
      exact sameCycle_iterate f n x
  -- the common middle count: orbits of `f` off `l`
  set S := Setoid.comap (Subtype.val : {x : A // x ∉ l} → A) (SameCycle.setoid f) with hS
  -- the `f` side
  have h1 : cycleCount f
      = Nat.card {q : Quotient (SameCycle.setoid f) // Meets _ (· ∈ l) q}
        + Nat.card {q : Quotient (SameCycle.setoid f) // ¬ Meets _ (· ∈ l) q} :=
    card_split _
  have h2 : Nat.card {q : Quotient (SameCycle.setoid f) // Meets _ (· ∈ l) q}
      = min l.length 1 := by
    match l, hcycle with
    | [], _ => simpa using card_meets_eq_zero (s := SameCycle.setoid f) (by simp)
    | x₀ :: t, hcycle =>
      have h := card_meets_eq_one (s := SameCycle.setoid f) (x₀ := x₀)
        (p := (· ∈ x₀ :: t)) (by simp) (fun x hx => hcycle x₀ (by simp) x hx)
      simpa using h
  have h3 : Nat.card (Quotient S)
      = Nat.card {q : Quotient (SameCycle.setoid f) // ¬ Meets _ (· ∈ l) q} := by
    rw [← card_subtype_true]
    refine card_quotient_eq Subtype.val _ _ (fun u v => Iff.rfl) ?_ ?_
    · intro u
      simp only [true_iff]
      rintro ⟨x, hx, hxl⟩
      exact u.2 ((sameCycle_iff_mem_aux (f := f) hl (Quotient.exact hx) hxl))
    · intro q hq
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      have hx : x ∉ l := fun hm => hq ⟨x, rfl, hm⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  -- the `fG` side
  have h4 : cycleCount fG
      = Nat.card {q : Quotient (SameCycle.setoid fG) // Meets _ (· ∈ Set.range b) q}
        + Nat.card {q : Quotient (SameCycle.setoid fG) // ¬ Meets _ (· ∈ Set.range b) q} :=
    card_split _
  have h5 : cycleCount g
      = Nat.card {q : Quotient (SameCycle.setoid fG) // Meets _ (· ∈ Set.range b) q} := by
    change Nat.card (Quotient (SameCycle.setoid g)) = _
    rw [← card_subtype_true]
    refine card_quotient_eq b _ _ hcycb ?_ ?_
    · intro y
      simp only [true_iff]
      exact ⟨b y, rfl, ⟨y, rfl⟩⟩
    · intro q hq
      obtain ⟨z, hz, y, rfl⟩ := hq
      exact ⟨y, hz⟩
  have h6 : Nat.card (Quotient S)
      = Nat.card {q : Quotient (SameCycle.setoid fG) // ¬ Meets _ (· ∈ Set.range b) q} := by
    rw [← card_subtype_true]
    refine card_quotient_eq (fun u : {x : A // x ∉ l} => a u.val) _ _
      (fun u v => hcyca u.val v.val u.2) ?_ ?_
    · intro u
      simp only [true_iff]
      rintro ⟨z, hz, hzb⟩
      have := (hinvb' (Quotient.exact hz)).mp hzb
      exact u.2 ((hmem u.val).mp this)
    · intro q hq
      obtain ⟨z, rfl⟩ := Quotient.exists_rep q
      have hz : z ∉ Set.range b := fun hm => hq ⟨z, rfl, hm⟩
      obtain ⟨x, rfl⟩ := hcover z hz
      exact ⟨⟨x, fun hm => hz ((hmem x).mpr hm)⟩, rfl⟩
  omega

/-- Transporting the equivalence closure along a map. -/
private theorem eqvGen_map {A B : Type*} {r : A → A → Prop} {s : B → B → Prop} (f : A → B)
    (h : ∀ x y, r x y → Relation.EqvGen s (f x) (f y)) {x y : A}
    (hxy : Relation.EqvGen r x y) : Relation.EqvGen s (f x) (f y) := by
  induction hxy with
  | rel x y hr => exact h x y hr
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Darts of a common orbit lie in a common component. -/
private theorem eqvGen_glink_of_cedge [Finite D] (H : Hypermap D) {x y : D}
    (h : H.CEdge x y) : Relation.EqvGen H.GLink x y := by
  have h' : Relation.ReflTransGen (fun a b => b = H.edge a) x y :=
    (sameCycle_iff_reflTransGen H.edge x y).mp h
  clear h
  induction h' with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (Or.inl hbc))

/-- Darts of a common node lie in a common component. -/
private theorem eqvGen_glink_of_cnode [Finite D] (H : Hypermap D) {x y : D}
    (h : H.CNode x y) : Relation.EqvGen H.GLink x y := by
  have h' : Relation.ReflTransGen (fun a b => b = H.node a) x y :=
    (sameCycle_iff_reflTransGen H.node x y).mp h
  clear h
  induction h' with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (Or.inr (Or.inl hbc)))

/-- Darts of a common face lie in a common component. -/
private theorem eqvGen_glink_of_cface [Finite D] (H : Hypermap D) {x y : D}
    (h : H.CFace x y) : Relation.EqvGen H.GLink x y := by
  have h' : Relation.ReflTransGen (fun a b => b = H.face a) x y :=
    (sameCycle_iff_reflTransGen H.face x y).mp h
  clear h
  induction h' with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (Or.inr (Or.inr hbc)))

/-- The class of a dart does not change along an E-link. -/
private theorem comp_edge (H : Hypermap D) (x : D) :
    Quotient.mk H.gcompSetoid (H.edge x) = Quotient.mk H.gcompSetoid x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (H.glink_edge x)))

/-- The class of a dart does not change along an N-link. -/
private theorem comp_node (H : Hypermap D) (x : D) :
    Quotient.mk H.gcompSetoid (H.node x) = Quotient.mk H.gcompSetoid x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (H.glink_node x)))

/-- The class of a dart does not change along an F-link. -/
private theorem comp_face (H : Hypermap D) (x : D) :
    Quotient.mk H.gcompSetoid (H.face x) = Quotient.mk H.gcompSetoid x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (H.glink_face x)))

/-! ### Plainness relative to a set of darts -/

/-- `G` is plain on `A`: every dart of `A` lies on an edge with exactly two
darts.  This is the edge analogue of `Hypermap.CubicOn`; the disk map of a
patch is only plain away from its border ring. -/
structure Hypermap.PlainOn (G : Hypermap D) (A : Set D) : Prop where
  /-- `edge` is an involution on `A`. -/
  edge_edge : ∀ x ∈ A, G.edge (G.edge x) = x
  /-- `edge` has no fixed dart in `A`. -/
  edge_ne : ∀ x ∈ A, G.edge x ≠ x

namespace Hypermap

/-- Being plain everywhere is being plain. -/
theorem plainOn_univ_iff {G : Hypermap D} : G.PlainOn Set.univ ↔ G.Plain :=
  ⟨fun h => ⟨fun x => h.edge_edge x (Set.mem_univ x), fun x => h.edge_ne x (Set.mem_univ x)⟩,
   fun h => ⟨fun x _ => h.edge_edge x, fun x _ => h.edge_ne x⟩⟩

/-- A plain hypermap is plain on every set of darts. -/
theorem Plain.plainOn {G : Hypermap D} (h : G.Plain) (A : Set D) : G.PlainOn A :=
  ⟨fun x _ => h.edge_edge x, fun x _ => h.edge_ne x⟩

end Hypermap

/-! ### The patch relation -/

/-- `Patch G Gd Gr hd hr bd br` says that `G` is the glueing of the disk map
`Gd` and the remainder map `Gr` along their border rings `bd` and `br`: the
injections `hd`, `hr` cover `G`, their images meet exactly along the ring, the
two rings traverse it in opposite directions, and away from the rings `hd`
preserves E-links while `hr` preserves N-links.  Both injections always
preserve the *other* permutation. -/
structure Patch (G : Hypermap D) (Gd : Hypermap Dd) (Gr : Hypermap Dr)
    (hd : Dd → D) (hr : Dr → D) (bd : List Dd) (br : List Dr) : Prop where
  /-- The disk embedding is injective. -/
  injd : Function.Injective hd
  /-- The remainder embedding is injective. -/
  injr : Function.Injective hr
  /-- The disk border is a face-simple E-cycle. -/
  scycle_d : Gd.Scycle (fun u v => v = Gd.edge u) bd
  /-- The remainder border is an N-cycle. -/
  cycle_r : IsCyclicChain (fun u v => v = Gr.node u) br
  /-- The remainder border has no repetitions. -/
  nodup_r : br.Nodup
  /-- The two borders traverse the ring in opposite directions. -/
  ring : br.map hr = (bd.map hd).reverse
  /-- The remainder covers everything outside the disk, plus the ring. -/
  range_r : ∀ x : D, x ∈ Set.range hr ↔ x ∉ Set.range hd ∨ x ∈ bd.map hd
  /-- Off its border the disk embedding preserves E-links. -/
  edge_d : ∀ ⦃xd : Dd⦄, xd ∉ bd → hd (Gd.edge xd) = G.edge (hd xd)
  /-- The disk embedding preserves N-links. -/
  node_d : ∀ xd : Dd, hd (Gd.node xd) = G.node (hd xd)
  /-- The remainder embedding preserves E-links. -/
  edge_r : ∀ xr : Dr, hr (Gr.edge xr) = G.edge (hr xr)
  /-- Off its border the remainder embedding preserves N-links. -/
  node_r : ∀ ⦃xr : Dr⦄, xr ∉ br → hr (Gr.node xr) = G.node (hr xr)

namespace Patch

variable {G : Hypermap D} {Gd : Hypermap Dd} {Gr : Hypermap Dr} {hd : Dd → D} {hr : Dr → D}
  {bd : List Dd} {br : List Dr}

/-! #### Elementary consequences -/

/-- The disk border has no repetitions. -/
theorem nodup_d (P : Patch G Gd Gr hd hr bd br) : bd.Nodup := P.scycle_d.nodup

/-- The disk border is face-simple. -/
theorem simple_d (P : Patch G Gd Gr hd hr bd br) : Gd.Simple bd := P.scycle_d.simple

/-- The ring, seen in `G`, has no repetitions. -/
theorem nodup_ring (P : Patch G Gd Gr hd hr bd br) : (bd.map hd).Nodup :=
  List.Nodup.map P.injd P.nodup_d

/-- The image of the disk is the complement of the remainder, plus the ring. -/
theorem range_d (P : Patch G Gd Gr hd hr bd br) (x : D) :
    x ∈ Set.range hd ↔ x ∉ Set.range hr ∨ x ∈ bd.map hd := by
  constructor
  · intro hx
    by_cases hxr : x ∈ Set.range hr
    · rcases (P.range_r x).mp hxr with h | h
      · exact absurd hx h
      · exact Or.inr h
    · exact Or.inl hxr
  · rintro (h | h)
    · by_contra hx
      exact h ((P.range_r x).mpr (Or.inl hx))
    · obtain ⟨u, _, rfl⟩ := List.mem_map.mp h
      exact ⟨u, rfl⟩

/-- The two images cover `G`. -/
theorem mem_range_or (P : Patch G Gd Gr hd hr bd br) (x : D) :
    x ∈ Set.range hd ∨ x ∈ Set.range hr := by
  by_cases h : x ∈ Set.range hd
  · exact Or.inl h
  · exact Or.inr ((P.range_r x).mpr (Or.inl h))

/-- The two border rings have the same image in `G`. -/
theorem mem_map_hr_iff (P : Patch G Gd Gr hd hr bd br) (x : D) :
    x ∈ br.map hr ↔ x ∈ bd.map hd := by
  rw [P.ring, List.mem_reverse]

/-- A disk dart lies in the image of the remainder exactly when it is on the
border. -/
theorem mem_bd_iff (P : Patch G Gd Gr hd hr bd br) (xd : Dd) :
    hd xd ∈ Set.range hr ↔ xd ∈ bd := by
  constructor
  · intro h
    rcases (P.range_r _).mp h with h' | h'
    · exact absurd ⟨xd, rfl⟩ h'
    · obtain ⟨u, hu, hux⟩ := List.mem_map.mp h'
      rwa [P.injd hux] at hu
  · intro h
    exact (P.range_r _).mpr (Or.inr (List.mem_map.mpr ⟨xd, h, rfl⟩))

/-- A remainder dart lies in the image of the disk exactly when it is on the
border. -/
theorem mem_br_iff (P : Patch G Gd Gr hd hr bd br) (xr : Dr) :
    hr xr ∈ Set.range hd ↔ xr ∈ br := by
  constructor
  · intro h
    rcases (P.range_d _).mp h with h' | h'
    · exact absurd ⟨xr, rfl⟩ h'
    · rw [← P.mem_map_hr_iff] at h'
      obtain ⟨u, hu, hux⟩ := List.mem_map.mp h'
      rwa [P.injr hux] at hu
  · intro h
    have hmem : hr xr ∈ br.map hr := List.mem_map.mpr ⟨xr, h, rfl⟩
    rw [P.mem_map_hr_iff] at hmem
    obtain ⟨u, _, hux⟩ := List.mem_map.mp hmem
    exact ⟨u, hux⟩

/-- The disk border is closed under `edge`. -/
theorem edge_mem_d_iff [Finite Dd] (P : Patch G Gd Gr hd hr bd br) (xd : Dd) :
    Gd.edge xd ∈ bd ↔ xd ∈ bd :=
  mem_iff_apply_mem P.scycle_d.isCyclicChain xd

/-- The remainder border is closed under `node`. -/
theorem node_mem_r_iff [Finite Dr] (P : Patch G Gd Gr hd hr bd br) (xr : Dr) :
    Gr.node xr ∈ br ↔ xr ∈ br :=
  mem_iff_apply_mem P.cycle_r xr

/-- The disk border is an edge orbit. -/
theorem cedge_mem_d [Finite Dd] (P : Patch G Gd Gr hd hr bd br) {xd : Dd} (hx : xd ∈ bd)
    (yd : Dd) : Gd.CEdge xd yd ↔ yd ∈ bd :=
  sameCycle_iff_mem P.scycle_d.isCyclicChain hx yd

/-- The remainder border is a node orbit. -/
theorem cnode_mem_r [Finite Dr] (P : Patch G Gd Gr hd hr bd br) {xr : Dr} (hx : xr ∈ br)
    (yr : Dr) : Gr.CNode xr yr ↔ yr ∈ br :=
  sameCycle_iff_mem P.cycle_r hx yr

/-! #### The ring correspondence -/

/-- The two border rings have the same length. -/
theorem length_br (P : Patch G Gd Gr hd hr bd br) : br.length = bd.length := by
  have h := congrArg List.length P.ring
  simpa using h

/-- Position `j` of the remainder border and position `i` of the disk border
name the same dart of `G` when the two positions are opposite. -/
theorem hr_getElem (P : Patch G Gd Gr hd hr bd br) {i j : ℕ} (hi : i < bd.length)
    (hj : j < br.length) (hij : i + j + 1 = bd.length) : hr br[j] = hd bd[i] := by
  have hmap : (br.map hr)[j]? = ((bd.map hd).reverse)[j]? := by rw [P.ring]
  rw [List.getElem?_map, List.getElem?_eq_getElem hj] at hmap
  rw [List.getElem?_reverse' (l := bd.map hd) (i := j) (j := i)
      (by simp only [List.length_map]; omega),
    List.getElem?_map, List.getElem?_eq_getElem hi] at hmap
  simpa using hmap

/-- Walking one step along the disk border applies `edge`. -/
theorem edge_getElem (P : Patch G Gd Gr hd hr bd br) {i k : ℕ} {hi : i < bd.length}
    {hk : k < bd.length} (hik : k = (i + 1) % bd.length) : Gd.edge bd[i] = bd[k] :=
  (getElem_succ P.scycle_d.isCyclicChain hik).symm

/-- Walking one step along the remainder border applies `node`. -/
theorem node_getElem (P : Patch G Gd Gr hd hr bd br) {j l : ℕ} {hj : j < br.length}
    {hl : l < br.length} (hjl : l = (j + 1) % br.length) : Gr.node br[j] = br[l] :=
  (getElem_succ P.cycle_r hjl).symm

/-- The key compatibility of the two glueings: crossing the ring from the disk
by an E-link is crossing it from the remainder by an N-link. -/
theorem hd_edge_eq_hr_iff [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    (xd : Dd) (xr : Dr) : hd (Gd.edge xd) = hr xr ↔ hd xd = hr (Gr.node xr) := by
  by_cases hxd : xd ∈ bd
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxd
    have hn : 0 < bd.length := by omega
    have hlen : br.length = bd.length := P.length_br
    obtain ⟨k, hk, hkdef⟩ : ∃ k, k < bd.length ∧ k = (i + 1) % bd.length :=
      ⟨_, Nat.mod_lt _ hn, rfl⟩
    have hk1 : bd.length - 1 - k < br.length := by omega
    have hk2 : bd.length - 1 - i < br.length := by omega
    have h1 := (P.hr_getElem hk hk1 (by omega)).symm
    have h2 := (P.hr_getElem hi hk2 (by omega)).symm
    rw [P.edge_getElem (hk := hk) hkdef, h1, h2]
    by_cases hxr : xr ∈ br
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxr
      obtain ⟨l, hl, hldef⟩ : ∃ l, l < br.length ∧ l = (j + 1) % br.length :=
        ⟨_, Nat.mod_lt _ (by omega), rfl⟩
      rw [P.node_getElem (hl := hl) hldef, P.injr.eq_iff, P.injr.eq_iff,
        List.Nodup.getElem_inj_iff P.nodup_r, List.Nodup.getElem_inj_iff P.nodup_r]
      exact cyclic_index_iff hi (by omega) hkdef (by rw [hldef, hlen])
    · constructor
      · intro h
        have hb : br[bd.length - 1 - k] ∈ br := List.getElem_mem _
        rw [P.injr h] at hb
        exact absurd hb hxr
      · intro h
        have hb : br[bd.length - 1 - i] ∈ br := List.getElem_mem _
        rw [P.injr h] at hb
        exact absurd ((P.node_mem_r_iff xr).mp hb) hxr
  · constructor
    · intro h
      exact absurd ((P.edge_mem_d_iff xd).mp ((P.mem_bd_iff _).mp ⟨xr, h.symm⟩)) hxd
    · intro h
      exact absurd ((P.mem_bd_iff xd).mp ⟨Gr.node xr, h.symm⟩) hxd

/-- Every dart of the disk border has a partner on the remainder border. -/
theorem exists_hr_of_mem_bd [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br) {xd : Dd}
    (hx : xd ∈ bd) : ∃ xr : Dr, hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by
  obtain ⟨u, hu⟩ := (P.mem_bd_iff xd).mpr hx
  refine ⟨Gr.face (Gr.edge u), ?_, ?_⟩
  · rw [P.hd_edge_eq_hr_iff, Gr.edgeK, hu]
  · rw [Gr.edgeK, hu]

/-- Every dart of the remainder border has a partner on the disk border. -/
theorem exists_hd_of_mem_br [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br) {xr : Dr}
    (hx : xr ∈ br) : ∃ xd : Dd, hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by
  obtain ⟨u, hu⟩ := (P.mem_br_iff xr).mpr hx
  refine ⟨Gd.node (Gd.face u), ?_, ?_⟩
  · rw [Gd.faceK, hu]
  · rw [← P.hd_edge_eq_hr_iff, Gd.faceK, hu]

/-! #### Faces -/

/-- Off its border the disk embedding preserves F-links. -/
theorem face_d [Finite Dd] (P : Patch G Gd Gr hd hr bd br) {xd : Dd} (hx : xd ∉ bd) :
    hd (Gd.face xd) = G.face (hd xd) := by
  have hnf : Gd.node (Gd.face xd) ∉ bd := by
    intro h
    exact hx (by simpa using (P.edge_mem_d_iff (Gd.node (Gd.face xd))).mpr h)
  have key : G.edge (G.node (hd (Gd.face xd))) = G.edge (G.node (G.face (hd xd))) := by
    rw [G.faceK, ← P.node_d, ← P.edge_d hnf, Gd.faceK]
  exact G.node.injective (G.edge.injective key)

/-- Where its image stays off the border the remainder embedding preserves
F-links. -/
theorem face_r (P : Patch G Gd Gr hd hr bd br) {xr : Dr} (hx : Gr.face xr ∉ br) :
    hr (Gr.face xr) = G.face (hr xr) := by
  have h := P.edge_r (Gr.node (Gr.face xr))
  rw [Gr.faceK, P.node_r hx] at h
  rw [h, G.nodeK]

/-- Crossing the ring commutes with taking faces. -/
theorem hd_face_eq_face_hr_iff [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    (xd : Dd) (xr : Dr) :
    hd (Gd.face xd) = G.face (hr xr) ↔ hd xd = hr (Gr.face xr) := by
  have hkey := P.hd_edge_eq_hr_iff (Gd.node (Gd.face xd)) (Gr.face xr)
  rw [Gd.faceK, P.node_d] at hkey
  rw [hkey]
  have hu : hr xr = G.edge (hr (Gr.node (Gr.face xr))) := by
    have h := P.edge_r (Gr.node (Gr.face xr))
    rwa [Gr.faceK] at h
  constructor
  · intro h
    rw [h, hu]
    exact G.edgeK _
  · intro h
    have h2 : G.face (G.edge (G.node (hd (Gd.face xd))))
        = G.face (G.edge (hr (Gr.node (Gr.face xr)))) := by rw [h]
    rw [G.nodeK, ← hu] at h2
    exact h2

/-! #### Face orbits -/

/-- The darts of `G` whose face meets the image of the remainder map.  This is
the reference development's `outer`. -/
def Outer (G : Hypermap D) (hr : Dr → D) : Set D := {x | ∃ xr : Dr, G.CFace x (hr xr)}

/-- The dart across the E-link of `hd xd`, as seen in the disk. -/
theorem face_edge_hd (P : Patch G Gd Gr hd hr bd br) (xd : Dd) :
    G.face (G.edge (hd xd)) = hd (Gd.face (Gd.edge xd)) := by
  have hxdw : hd xd = G.node (hd (Gd.face (Gd.edge xd))) := by rw [← P.node_d, Gd.edgeK]
  rw [hxdw, G.nodeK]

/-- Walking around the face of a border dart returns to the border, and the
darts strictly in between lie off the border.  Here `k` is the number of face
steps spent inside the disk. -/
private theorem border_return [Finite Dd] (P : Patch G Gd Gr hd hr bd br) {u : Dd}
    (hu : u ∈ bd) : ∃ k : ℕ, Gd.face^[k + 1] u = u ∧ (∀ j < k, Gd.face^[j + 1] u ∉ bd) ∧
      ∀ j ≤ k, hd (Gd.face^[j + 1] u) = G.face^[j] (hd (Gd.face u)) := by
  classical
  have hex : ∃ k, Gd.face^[k + 1] u ∈ bd := by
    refine ⟨Gd.arity u - 1, ?_⟩
    have hpos := Gd.arity_pos u
    rw [show Gd.arity u - 1 + 1 = Gd.arity u by omega, Gd.iterate_face_arity u]
    exact hu
  refine ⟨Nat.find hex, ?_, fun j hj => Nat.find_min hex hj, ?_⟩
  · exact P.simple_d.eq_of_cface (Nat.find_spec hex) hu (cface_iterate Gd _ u).symm
  · intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hnb : Gd.face^[j + 1] u ∉ bd := Nat.find_min hex (by omega)
      rw [Function.iterate_succ_apply' Gd.face (j + 1) u, P.face_d hnb, ih (by omega),
        Function.iterate_succ_apply' G.face j]

/-- `hd` maps F-links of the disk to F-paths of `G`. -/
theorem cface_hd [Finite Dd] (P : Patch G Gd Gr hd hr bd br) (xd : Dd) :
    G.CFace (hd xd) (hd (Gd.face xd)) := by
  by_cases hxd : xd ∈ bd
  · obtain ⟨k, hk, -, hstep⟩ := P.border_return hxd
    have hres := hstep k le_rfl
    rw [hk] at hres
    rw [hres]
    exact (cface_iterate G k (hd (Gd.face xd))).symm
  · rw [P.face_d hxd]
    exact G.cface_face (hd xd)

/-- `hd` maps face orbits of the disk into face orbits of `G`. -/
theorem cface_of_cface_d [Finite Dd] (P : Patch G Gd Gr hd hr bd br) {xd yd : Dd}
    (h : Gd.CFace xd yd) : G.CFace (hd xd) (hd yd) := by
  have key : ∀ n : ℕ, G.CFace (hd xd) (hd (Gd.face^[n] xd)) := by
    intro n
    induction n with
    | zero => simpa using SameCycle.refl G.face (hd xd)
    | succ n ih =>
      rw [Function.iterate_succ_apply' Gd.face n xd]
      exact ih.trans (P.cface_hd _)
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Perm.coe_pow] at hn
  rw [← hn]
  exact key n

/-- In the kernel of the border, `hd` commutes with iterated `face`. -/
theorem iterate_face_d [Finite Dd] (P : Patch G Gd Gr hd hr bd br) {xd : Dd}
    (hx : Gd.Kernel bd xd) (n : ℕ) : hd (Gd.face^[n] xd) = G.face^[n] (hd xd) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hker : Gd.Kernel bd (Gd.face^[n] xd) := by
      rintro ⟨y, hy, hcy⟩
      exact hx ⟨y, hy, (cface_iterate Gd n xd).trans hcy⟩
    have hnb : Gd.face^[n] xd ∉ bd := fun hmem => hker ⟨_, hmem, SameCycle.refl _ _⟩
    rw [Function.iterate_succ_apply' Gd.face n xd, P.face_d hnb, ih,
      Function.iterate_succ_apply' G.face n]

/-- A disk dart lies under the outer band exactly when it lies in the face band
of the border. -/
theorem mem_outer_hd_iff [Finite D] [Finite Dd] (P : Patch G Gd Gr hd hr bd br) (xd : Dd) :
    hd xd ∈ Outer G hr ↔ Gd.Fband bd xd := by
  constructor
  · intro hx
    by_contra hb
    obtain ⟨xr, hxr⟩ := hx
    obtain ⟨n, hn⟩ := hxr.exists_nat_pow_eq
    rw [Perm.coe_pow, ← P.iterate_face_d hb n] at hn
    have hmem : Gd.face^[n] xd ∈ bd := (P.mem_bd_iff _).mp ⟨xr, hn.symm⟩
    exact hb ⟨_, hmem, cface_iterate Gd n xd⟩
  · rintro ⟨yd, hyd, hxy⟩
    obtain ⟨xr, hxr⟩ := (P.mem_bd_iff yd).mpr hyd
    exact ⟨xr, (P.cface_of_cface_d hxy).trans (by rw [hxr])⟩

/-- Off the outer band, `hd` reflects face orbits. -/
theorem cface_hd_iff [Finite D] [Finite Dd] (P : Patch G Gd Gr hd hr bd br) {xd yd : Dd}
    (hx : hd xd ∉ Outer G hr) : Gd.CFace xd yd ↔ G.CFace (hd xd) (hd yd) := by
  refine ⟨fun h => P.cface_of_cface_d h, fun h => ?_⟩
  have hb : Gd.Kernel bd xd := fun hfb => hx ((P.mem_outer_hd_iff xd).mpr hfb)
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Perm.coe_pow, ← P.iterate_face_d hb n] at hn
  rw [← P.injd hn]
  exact cface_iterate Gd n xd

/-- When the next dart of a remainder face lies on the border, the face of `G`
continues into the disk. -/
theorem face_hr_of_mem_br [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br) {xr : Dr}
    (hx : Gr.face xr ∈ br) : ∃ xd : Dd, hd (Gd.edge xd) = hr (Gr.face xr) ∧
      G.face (hr xr) = hd (Gd.face (Gd.edge xd)) := by
  obtain ⟨xd, h1, h2⟩ := P.exists_hd_of_mem_br hx
  refine ⟨xd, h1, ?_⟩
  have hxr : hr xr = G.edge (hd xd) := by
    have h := P.edge_r (Gr.node (Gr.face xr))
    rw [Gr.faceK, ← h2] at h
    exact h
  rw [hxr]
  exact P.face_edge_hd xd

/-- The face orbit of a remainder dart returns to the image of the remainder
map exactly at the next dart of its face in `Gr`. -/
private theorem face_return_r [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    (xr : Dr) : ∃ d : ℕ, 0 < d ∧ G.face^[d] (hr xr) = hr (Gr.face xr) ∧
      ∀ i, 0 < i → i < d → G.face^[i] (hr xr) ∉ Set.range hr := by
  by_cases hfx : Gr.face xr ∈ br
  · obtain ⟨xd, h1, hface1⟩ := P.face_hr_of_mem_br hfx
    have hu : Gd.edge xd ∈ bd := (P.mem_bd_iff _).mp ⟨Gr.face xr, h1.symm⟩
    obtain ⟨k, hk, hmin, hstep⟩ := P.border_return hu
    refine ⟨k + 1, Nat.succ_pos k, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hface1]
      have hlast := hstep k le_rfl
      rw [hk] at hlast
      rw [← hlast, h1]
    · intro i hi0 hik
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [Function.iterate_succ_apply, hface1, ← hstep j (by omega)]
      intro hmem
      exact hmin j (by omega) ((P.mem_bd_iff _).mp hmem)
  · exact ⟨1, Nat.one_pos, by simpa using (P.face_r hfx).symm, fun i h1 h2 => absurd h2 (by omega)⟩

/-- `hr` maps F-links of the remainder to F-paths of `G`. -/
theorem cface_hr [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br) (xr : Dr) :
    G.CFace (hr xr) (hr (Gr.face xr)) := by
  obtain ⟨d, -, hdeq, -⟩ := P.face_return_r xr
  rw [← hdeq]
  exact cface_iterate G d (hr xr)

/-- Face orbits of `G` meeting the remainder come from face orbits of `Gr`. -/
private theorem cface_of_iterate [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br) :
    ∀ n : ℕ, ∀ xr yr : Dr, G.face^[n] (hr xr) = hr yr → Gr.CFace xr yr := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xr yr hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [Function.iterate_zero, id_eq] at hn
      rw [P.injr hn]
    · obtain ⟨d, hd0, hdeq, hdmin⟩ := P.face_return_r xr
      rcases Nat.lt_or_ge n d with hnd | hnd
      · exact absurd ⟨yr, hn.symm⟩ (hdmin n hpos hnd)
      · have hsplit : G.face^[n - d] (hr (Gr.face xr)) = hr yr := by
          rw [← hdeq, ← Function.iterate_add_apply, Nat.sub_add_cancel hnd]
          exact hn
        exact sameCycle_apply_left.mp (ih (n - d) (by omega) (Gr.face xr) yr hsplit)

/-- `hr` both preserves and reflects face orbits. -/
theorem cface_hr_iff [Finite D] [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    (xr yr : Dr) : Gr.CFace xr yr ↔ G.CFace (hr xr) (hr yr) := by
  constructor
  · intro h
    have key : ∀ n : ℕ, G.CFace (hr xr) (hr (Gr.face^[n] xr)) := by
      intro n
      induction n with
      | zero => simpa using SameCycle.refl G.face (hr xr)
      | succ n ih =>
        rw [Function.iterate_succ_apply' Gr.face n xr]
        exact ih.trans (P.cface_hr _)
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [Perm.coe_pow] at hn
    rw [← hn]
    exact key n
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [Perm.coe_pow] at hn
    exact P.cface_of_iterate n xr yr hn

/-! #### Bridges -/

/-- Bridgelessness passes to both parts. -/
theorem bridgeless [Finite D] [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    (h : G.Bridgeless) : Gd.Bridgeless ∧ Gr.Bridgeless := by
  constructor
  · intro xd hxd
    refine h (hd xd) ?_
    have h1 : G.CFace (hd xd) (hd (Gd.edge xd)) := P.cface_of_cface_d hxd
    have h2 : G.CFace (hd (Gd.edge xd)) (hd (Gd.face (Gd.edge xd))) := P.cface_hd _
    have h3 : G.CFace (G.edge (hd xd)) (hd (Gd.face (Gd.edge xd))) := by
      rw [← P.face_edge_hd xd]
      exact G.cface_face _
    exact (h1.trans h2).trans h3.symm
  · intro xr hxr
    refine h (hr xr) ?_
    rw [← P.edge_r]
    exact (P.cface_hr_iff xr (Gr.edge xr)).mp hxr

/-- **Bridgelessness of a patch**: if both parts are bridgeless and the disk
border has no chords, the patched map is bridgeless. -/
theorem bridgeless_patch [Finite D] [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    (hGd : Gd.Bridgeless) (hGr : Gr.Bridgeless) (hch : Gd.Chordless bd) : G.Bridgeless := by
  intro x hx
  by_cases hxr : x ∈ Set.range hr
  · obtain ⟨xr, rfl⟩ := hxr
    refine hGr xr ?_
    rw [P.cface_hr_iff, P.edge_r]
    exact hx
  · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
    have hxd : xd ∉ bd := fun hb => hxr ((P.mem_bd_iff xd).mpr hb)
    rw [← P.edge_d hxd] at hx
    by_cases hout : hd xd ∈ Outer G hr
    · obtain ⟨yd, hyd, hxy⟩ := (P.mem_outer_hd_iff xd).mp hout
      have hout2 : hd (Gd.edge xd) ∈ Outer G hr := by
        obtain ⟨w, hw⟩ := hout
        exact ⟨w, hx.symm.trans hw⟩
      obtain ⟨zd, hzd, hxz⟩ := (P.mem_outer_hd_iff (Gd.edge xd)).mp hout2
      have hkey : G.CFace (hd yd) (hd zd) :=
        ((P.cface_of_cface_d hxy).symm.trans hx).trans (P.cface_of_cface_d hxz)
      have hadj : Gd.Adj yd zd := ⟨xd, hxy.symm, hxz⟩
      rcases hch yd hyd zd hzd hadj with rfl | hnext | hnext
      · exact hGd xd (hxy.trans hxz.symm)
      · have hze : zd = Gd.edge yd := cyclicNext_eq P.scycle_d.isCyclicChain hnext
        obtain ⟨yr, h1, h2⟩ := P.exists_hr_of_mem_bd hyd
        refine hGr (Gr.node yr) ?_
        have hA : Gr.CFace (Gr.edge (Gr.node yr)) yr := by
          have h := Gr.cface_face (Gr.edge (Gr.node yr))
          rwa [Gr.nodeK] at h
        have hB : Gr.CFace (Gr.node yr) yr := by
          rw [P.cface_hr_iff, ← h1, ← h2, ← hze]
          exact hkey
        exact hB.trans hA.symm
      · have hze : yd = Gd.edge zd := cyclicNext_eq P.scycle_d.isCyclicChain hnext
        obtain ⟨zr, h1, h2⟩ := P.exists_hr_of_mem_bd hzd
        refine hGr (Gr.node zr) ?_
        have hA : Gr.CFace (Gr.edge (Gr.node zr)) zr := by
          have h := Gr.cface_face (Gr.edge (Gr.node zr))
          rwa [Gr.nodeK] at h
        have hB : Gr.CFace (Gr.node zr) zr := by
          rw [P.cface_hr_iff, ← h1, ← h2, ← hze]
          exact hkey.symm
        exact hB.trans hA.symm
    · refine hGd xd ?_
      rw [P.cface_hd_iff hout]
      exact hx

/-! #### Colourings -/

/-- Two colourings of the parts that match along the ring agree at every pair of
darts glued together. -/
theorem eq_of_ring_eq (P : Patch G Gd Gr hd hr bd br) {kd : Dd → Color} {kr : Dr → Color}
    (hring : (bd.map kd).reverse = br.map kr) {xd : Dd} {xr : Dr} (hx : hd xd = hr xr) :
    kd xd = kr xr := by
  have hxd : xd ∈ bd := (P.mem_bd_iff xd).mp ⟨xr, hx.symm⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxd
  have hlen : br.length = bd.length := P.length_br
  have hj : bd.length - 1 - i < br.length := by omega
  have hxr : br[bd.length - 1 - i] = xr := P.injr (by rw [P.hr_getElem hi hj (by omega), hx])
  rw [← hxr]
  have hmap : ((bd.map kd).reverse)[bd.length - 1 - i]? = (br.map kr)[bd.length - 1 - i]? := by
    rw [hring]
  rw [List.getElem?_reverse' (l := bd.map kd) (i := bd.length - 1 - i) (j := i)
      (by simp only [List.length_map]; omega),
    List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_map,
    List.getElem?_eq_getElem hj] at hmap
  simpa using hmap

/-- **Colouring a patch**: `G` is four-colourable exactly when the two parts
admit colourings whose ring traces match. -/
theorem colorable_patch [Finite D] [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br) :
    G.FourColorable ↔
      ∃ et : List Color, Gd.RingTrace bd et ∧ Gr.RingTrace br ((et.reverse).rotate 1) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨trace (bd.map (k ∘ hd)), ⟨k ∘ hd, ⟨?_, ?_⟩, rfl⟩, ⟨k ∘ hr, ⟨?_, ?_⟩, ?_⟩⟩
    · intro xd
      simp only [Function.comp_apply]
      intro hcon
      have h1 : k (hd (Gd.edge xd)) = k (hd (Gd.face (Gd.edge xd))) :=
        coloring_cface hk (P.cface_hd _)
      have h2 : k (hd xd) = k (G.node (hd (Gd.face (Gd.edge xd)))) := by
        rw [← P.node_d, Gd.edgeK]
      have h3 : k (G.edge (G.node (hd (Gd.face (Gd.edge xd)))))
          = k (hd (Gd.face (Gd.edge xd))) := by
        have h := hk.face (G.edge (G.node (hd (Gd.face (Gd.edge xd)))))
        rw [G.nodeK] at h
        exact h.symm
      exact hk.edge (G.node (hd (Gd.face (Gd.edge xd)))) (by rw [h3, ← h1, hcon, h2])
    · intro xd
      simp only [Function.comp_apply]
      exact (coloring_cface hk (P.cface_hd xd)).symm
    · intro xr
      simp only [Function.comp_apply]
      rw [P.edge_r]
      exact hk.edge (hr xr)
    · intro xr
      simp only [Function.comp_apply]
      exact (coloring_cface hk (P.cface_hr xr)).symm
    · have hmap : br.map (k ∘ hr) = (bd.map (k ∘ hd)).reverse := by
        rw [← List.map_map, ← List.map_map, P.ring, List.map_reverse]
      rw [hmap, trace_reverse]
  · rintro ⟨et, ⟨kd0, hkd0, hetd⟩, ⟨kr, hkr, hetr⟩⟩
    classical
    have hlenAB : ((bd.map kd0).reverse).length = (br.map kr).length := by
      simp [P.length_br]
    have htr : trace ((bd.map kd0).reverse) = trace (br.map kr) := by
      rw [trace_reverse, ← hetd, ← hetr]
    have hmatch := eq_map_add_of_trace_eq hlenAB htr
    set cshift := ((bd.map kd0).reverse).headD 0 + (br.map kr).headD 0 with hcshift
    set kd : Dd → Color := fun xd => cshift + kd0 xd with hkddef
    have hkd : Gd.Coloring kd := hkd0.comp (add_right_injective cshift)
    have hring : (bd.map kd).reverse = br.map kr := by
      have h1 : bd.map kd = (bd.map kd0).map (cshift + ·) := by
        rw [List.map_map]
        rfl
      rw [h1, ← List.map_reverse]
      exact hmatch.symm
    have heq : ∀ (xd : Dd) (xr : Dr), hd xd = hr xr → kd xd = kr xr :=
      fun xd xr hx => P.eq_of_ring_eq hring hx
    obtain ⟨k, hkr', hkd'⟩ :
        ∃ k : D → Color, (∀ xr, k (hr xr) = kr xr) ∧ ∀ xd, k (hd xd) = kd xd := by
      refine ⟨fun x => if h : ∃ xr : Dr, hr xr = x then kr h.choose
        else if h' : ∃ xd : Dd, hd xd = x then kd h'.choose else 0, ?_, ?_⟩
      · intro xr
        dsimp only
        have hex : ∃ yr : Dr, hr yr = hr xr := ⟨xr, rfl⟩
        rw [dite_eq_left hex]
        exact congrArg kr (P.injr hex.choose_spec)
      · intro xd
        dsimp only
        by_cases hex : ∃ yr : Dr, hr yr = hd xd
        · rw [dite_eq_left hex]
          exact (heq xd hex.choose hex.choose_spec.symm).symm
        · rw [dite_eq_right hex]
          have hex' : ∃ yd : Dd, hd yd = hd xd := ⟨xd, rfl⟩
          rw [dite_eq_left hex']
          exact congrArg kd (P.injd hex'.choose_spec)
    refine ⟨k, ⟨?_, ?_⟩⟩
    · intro x
      by_cases hxr : x ∈ Set.range hr
      · obtain ⟨xr, rfl⟩ := hxr
        rw [← P.edge_r, hkr', hkr']
        exact hkr.edge xr
      · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
        have hxd : xd ∉ bd := fun hb => hxr ((P.mem_bd_iff xd).mpr hb)
        rw [← P.edge_d hxd, hkd', hkd']
        exact hkd.edge xd
    · intro x
      by_cases hxr : x ∈ Set.range hr
      · obtain ⟨xr, rfl⟩ := hxr
        by_cases hfx : Gr.face xr ∈ br
        · obtain ⟨xd, h1, h2⟩ := P.face_hr_of_mem_br hfx
          rw [h2, hkd', hkd.face, hkr']
          exact (heq _ _ h1).trans (hkr.face xr)
        · rw [← P.face_r hfx, hkr', hkr']
          exact hkr.face xr
      · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
        have hxd : xd ∉ bd := fun hb => hxr ((P.mem_bd_iff xd).mpr hb)
        rw [← P.face_d hxd, hkd', hkd']
        exact hkd.face xd

/-! #### Components -/

/-- Components of the disk map become components of `G`. -/
private theorem eqvGen_glink_hd [Finite D] [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    {xd yd : Dd} (h : Relation.EqvGen Gd.GLink xd yd) :
    Relation.EqvGen G.GLink (hd xd) (hd yd) := by
  refine eqvGen_map hd (fun a b hab => ?_) h
  rcases hab with rfl | rfl | rfl
  · have h2 : hd a = G.node (hd (Gd.face (Gd.edge a))) := by rw [← P.node_d, Gd.edgeK]
    refine Relation.EqvGen.trans _ _ _ ?_ (eqvGen_glink_of_cface G (P.cface_hd (Gd.edge a))).symm
    exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ (show G.GLink (hd (Gd.face (Gd.edge a))) (hd a) from
        Or.inr (Or.inl h2)))
  · exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl (P.node_d a)))
  · exact eqvGen_glink_of_cface G (P.cface_hd a)

/-- Components of the remainder map become components of `G`. -/
private theorem eqvGen_glink_hr [Finite D] [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    {xr yr : Dr} (h : Relation.EqvGen Gr.GLink xr yr) :
    Relation.EqvGen G.GLink (hr xr) (hr yr) := by
  refine eqvGen_map hr (fun a b hab => ?_) h
  rcases hab with rfl | rfl | rfl
  · exact Relation.EqvGen.rel _ _ (Or.inl (P.edge_r a))
  · have hv : hr (Gr.edge (Gr.node a)) = G.edge (hr (Gr.node a)) := P.edge_r _
    have hfa : Gr.face (Gr.edge (Gr.node a)) = a := Gr.nodeK a
    refine Relation.EqvGen.trans _ _ _ ?_
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        (show G.GLink (hr (Gr.node a)) (hr (Gr.edge (Gr.node a))) from Or.inl hv)))
    have hc := eqvGen_glink_of_cface G (P.cface_hr (Gr.edge (Gr.node a)))
    rw [hfa] at hc
    exact hc.symm
  · exact eqvGen_glink_of_cface G (P.cface_hr a)

open scoped Classical in
/-- The disk component attached to a dart of `G`: the component of its disk
preimage when it has one, and the component of the ring otherwise. -/
private noncomputable def diskComp (Gd : Hypermap Dd) (hd : Dd → D) (bd : List Dd) (x : D) :
    Option (Quotient Gd.gcompSetoid) :=
  if h : x ∈ Set.range hd then some (Quotient.mk _ h.choose)
  else bd.head?.map (Quotient.mk _)

open scoped Classical in
/-- The remainder component attached to a dart of `G`. -/
private noncomputable def remComp (Gr : Hypermap Dr) (hr : Dr → D) (br : List Dr) (x : D) :
    Option (Quotient Gr.gcompSetoid) :=
  if h : x ∈ Set.range hr then some (Quotient.mk _ h.choose)
  else br.head?.map (Quotient.mk _)

/-- All darts of the disk border lie in one component of the disk. -/
private theorem ring_comp_d [Finite Dd] (P : Patch G Gd Gr hd hr bd br) {zd : Dd}
    (hz : zd ∈ bd) : bd.head?.map (Quotient.mk Gd.gcompSetoid) = some (Quotient.mk _ zd) := by
  rcases bd with _ | ⟨z, t⟩
  · exact absurd hz (by simp)
  · simp only [List.head?_cons, Option.map_some]
    exact congrArg _ (Quotient.sound
      (eqvGen_glink_of_cedge Gd ((P.cedge_mem_d (by simp) zd).mpr hz)))

/-- All darts of the remainder border lie in one component of the remainder. -/
private theorem ring_comp_r [Finite Dr] (P : Patch G Gd Gr hd hr bd br) {zr : Dr}
    (hz : zr ∈ br) : br.head?.map (Quotient.mk Gr.gcompSetoid) = some (Quotient.mk _ zr) := by
  rcases br with _ | ⟨z, t⟩
  · exact absurd hz (by simp)
  · simp only [List.head?_cons, Option.map_some]
    exact congrArg _ (Quotient.sound
      (eqvGen_glink_of_cnode Gr ((P.cnode_mem_r (by simp) zr).mpr hz)))

private theorem diskComp_hd (P : Patch G Gd Gr hd hr bd br) (xd : Dd) :
    diskComp Gd hd bd (hd xd) = some (Quotient.mk _ xd) := by
  classical
  have hx : hd xd ∈ Set.range hd := ⟨xd, rfl⟩
  simp only [diskComp, dite_eq_left hx]
  exact congrArg _ (congrArg _ (P.injd hx.choose_spec))

private theorem remComp_hr (P : Patch G Gd Gr hd hr bd br) (xr : Dr) :
    remComp Gr hr br (hr xr) = some (Quotient.mk _ xr) := by
  classical
  have hx : hr xr ∈ Set.range hr := ⟨xr, rfl⟩
  simp only [remComp, dite_eq_left hx]
  exact congrArg _ (congrArg _ (P.injr hx.choose_spec))

private theorem diskComp_hr [Finite Dd] (P : Patch G Gd Gr hd hr bd br) (xr : Dr) :
    diskComp Gd hd bd (hr xr) = bd.head?.map (Quotient.mk _) := by
  classical
  by_cases h : hr xr ∈ Set.range hd
  · obtain ⟨zd, hzd⟩ := h
    rw [← hzd, diskComp_hd P zd]
    exact (ring_comp_d P ((P.mem_bd_iff zd).mp ⟨xr, hzd.symm⟩)).symm
  · simp only [diskComp, dite_eq_right h]

private theorem remComp_hd [Finite Dr] (P : Patch G Gd Gr hd hr bd br) (xd : Dd) :
    remComp Gr hr br (hd xd) = br.head?.map (Quotient.mk _) := by
  classical
  by_cases h : hd xd ∈ Set.range hr
  · obtain ⟨zr, hzr⟩ := h
    rw [← hzr, remComp_hr P zr]
    exact (ring_comp_r P ((P.mem_br_iff zr).mp ⟨xd, hzr.symm⟩)).symm
  · simp only [remComp, dite_eq_right h]

/-- The disk component of a dart does not change along a link of `G`. -/
private theorem diskComp_glink [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) {x y : D} (hxy : G.GLink x y) :
    diskComp Gd hd bd x = diskComp Gd hd bd y := by
  classical
  by_cases hxr : x ∈ Set.range hr
  · obtain ⟨xr, rfl⟩ := hxr
    rw [diskComp_hr P xr]
    rcases hxy with rfl | rfl | rfl
    · rw [← P.edge_r, diskComp_hr P]
    · by_cases hb : xr ∈ br
      · obtain ⟨xd, hxd⟩ := (P.mem_br_iff xr).mpr hb
        have hxdb : xd ∈ bd := (P.mem_bd_iff xd).mp ⟨xr, hxd.symm⟩
        rw [← hxd, ← P.node_d, diskComp_hd P, comp_node]
        exact ring_comp_d P hxdb
      · rw [← P.node_r hb, diskComp_hr P]
    · by_cases hfx : Gr.face xr ∈ br
      · obtain ⟨zd, h1, h2⟩ := P.face_hr_of_mem_br hfx
        have hzb : Gd.edge zd ∈ bd := (P.mem_bd_iff _).mp ⟨Gr.face xr, h1.symm⟩
        rw [h2, diskComp_hd P, comp_face]
        exact ring_comp_d P hzb
      · rw [← P.face_r hfx, diskComp_hr P]
  · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
    have hxdb : xd ∉ bd := fun hb => hxr ((P.mem_bd_iff xd).mpr hb)
    rw [diskComp_hd P xd]
    rcases hxy with rfl | rfl | rfl
    · rw [← P.edge_d hxdb, diskComp_hd P, comp_edge]
    · rw [← P.node_d, diskComp_hd P, comp_node]
    · rw [← P.face_d hxdb, diskComp_hd P, comp_face]

/-- The remainder component of a dart does not change along a link of `G`. -/
private theorem remComp_glink [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) {x y : D} (hxy : G.GLink x y) :
    remComp Gr hr br x = remComp Gr hr br y := by
  classical
  by_cases hxd : x ∈ Set.range hd
  · obtain ⟨xd, rfl⟩ := hxd
    rw [remComp_hd P xd]
    by_cases hb : xd ∈ bd
    · obtain ⟨xr, hxr⟩ := (P.mem_bd_iff xd).mpr hb
      have hxrb : xr ∈ br := (P.mem_br_iff xr).mp ⟨xd, hxr.symm⟩
      rcases hxy with rfl | rfl | rfl
      · rw [← hxr, ← P.edge_r, remComp_hr P, comp_edge]
        exact ring_comp_r P hxrb
      · rw [← P.node_d, remComp_hd P]
      · by_cases hfx : Gr.face xr ∈ br
        · obtain ⟨zd, h1, h2⟩ := P.face_hr_of_mem_br hfx
          rw [← hxr, h2, remComp_hd P]
        · rw [← hxr, ← P.face_r hfx, remComp_hr P, comp_face]
          exact ring_comp_r P hxrb
    · rcases hxy with rfl | rfl | rfl
      · rw [← P.edge_d hb, remComp_hd P]
      · rw [← P.node_d, remComp_hd P]
      · rw [← P.face_d hb, remComp_hd P]
  · obtain ⟨xr, rfl⟩ := (P.mem_range_or x).resolve_left hxd
    have hxrb : xr ∉ br := fun hb => hxd ((P.mem_br_iff xr).mpr hb)
    rw [remComp_hr P xr]
    rcases hxy with rfl | rfl | rfl
    · rw [← P.edge_r, remComp_hr P, comp_edge]
    · rw [← P.node_r hxrb, remComp_hr P, comp_node]
    · by_cases hfx : Gr.face xr ∈ br
      · obtain ⟨zd, h1, h2⟩ := P.face_hr_of_mem_br hfx
        rw [h2, remComp_hd P, ring_comp_r P hfx, comp_face]
      · rw [← P.face_r hfx, remComp_hr P, comp_face]

/-- The disk component of a dart is a component invariant of `G`. -/
private theorem diskComp_eqvGen [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) {x y : D} (h : Relation.EqvGen G.GLink x y) :
    diskComp Gd hd bd x = diskComp Gd hd bd y := by
  induction h with
  | rel x y hxy => exact diskComp_glink P hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The remainder component of a dart is a component invariant of `G`. -/
private theorem remComp_eqvGen [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) {x y : D} (h : Relation.EqvGen G.GLink x y) :
    remComp Gr hr br x = remComp Gr hr br y := by
  induction h with
  | rel x y hxy => exact remComp_glink P hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `hd` preserves and reflects components. -/
private theorem eqvGen_glink_hd_iff [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) {xd yd : Dd} :
    Relation.EqvGen Gd.GLink xd yd ↔ Relation.EqvGen G.GLink (hd xd) (hd yd) := by
  refine ⟨eqvGen_glink_hd P, fun h => ?_⟩
  have hc := diskComp_eqvGen P h
  rw [diskComp_hd P, diskComp_hd P] at hc
  exact Quotient.exact (Option.some.inj hc)

/-- `hr` preserves and reflects components. -/
private theorem eqvGen_glink_hr_iff [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) {xr yr : Dr} :
    Relation.EqvGen Gr.GLink xr yr ↔ Relation.EqvGen G.GLink (hr xr) (hr yr) := by
  refine ⟨eqvGen_glink_hr P, fun h => ?_⟩
  have hc := remComp_eqvGen P h
  rw [remComp_hr P, remComp_hr P] at hc
  exact Quotient.exact (Option.some.inj hc)

/-! #### Counting the orbits of a patch -/

/-- The E-cycles of the two parts are the E-cycles of `G`, plus the ring. -/
private theorem cycleCount_edge_patch [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) :
    cycleCount Gd.edge + cycleCount Gr.edge = cycleCount G.edge + min bd.length 1 :=
  cycleCount_pair P.injd P.injr P.edge_r (fun _ hx => P.edge_d hx) (P.edge_mem_d_iff)
    (fun z hz => (P.mem_range_or z).resolve_right hz) P.mem_bd_iff
    (fun _ hx y hy => (P.cedge_mem_d hx y).mpr hy)

/-- The N-cycles of the two parts are the N-cycles of `G`, plus the ring. -/
private theorem cycleCount_node_patch [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) :
    cycleCount Gd.node + cycleCount Gr.node = cycleCount G.node + min bd.length 1 := by
  have h := cycleCount_pair (f := Gr.node) (g := Gd.node) (fG := G.node) (a := hr) (b := hd)
    (l := br) P.injr P.injd P.node_d (fun _ hx => P.node_r hx) (P.node_mem_r_iff)
    (fun z hz => (P.mem_range_or z).resolve_left hz) P.mem_br_iff
    (fun x hx y hy => (P.cnode_mem_r hx y).mpr hy)
  rw [P.length_br] at h
  omega

/-- The faces of the two parts are the faces of `G`, plus one for each dart of
the ring: the ring is face-simple in the disk, so the ring darts lie in as many
different disk faces. -/
private theorem cycleCount_face_patch [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) :
    cycleCount Gd.face + cycleCount Gr.face = cycleCount G.face + bd.length := by
  classical
  set S := Setoid.comap (Subtype.val : {xd : Dd // Gd.Kernel bd xd} → Dd)
    (SameCycle.setoid Gd.face) with hS
  -- the disk side
  have h1 : cycleCount Gd.face
      = Nat.card {q : Quotient (SameCycle.setoid Gd.face) // Meets _ (· ∈ bd) q}
        + Nat.card {q : Quotient (SameCycle.setoid Gd.face) // ¬ Meets _ (· ∈ bd) q} :=
    card_split _
  have h2 : Nat.card {q : Quotient (SameCycle.setoid Gd.face) // Meets _ (· ∈ bd) q}
      = bd.length := by
    rw [← card_mem_list P.nodup_d]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun u : {xd : Dd // xd ∈ bd} => (⟨Quotient.mk _ u.val, ⟨u.val, rfl, u.2⟩⟩ :
        {q : Quotient (SameCycle.setoid Gd.face) // Meets _ (· ∈ bd) q})) ⟨?_, ?_⟩)).symm
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ heq
      exact Subtype.ext (P.simple_d.eq_of_cface hx hy (Quotient.exact (congrArg Subtype.val heq)))
    · rintro ⟨q, x, rfl, hx⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h3 : Nat.card (Quotient S)
      = Nat.card {q : Quotient (SameCycle.setoid Gd.face) // ¬ Meets _ (· ∈ bd) q} := by
    rw [← card_subtype_true]
    refine card_quotient_eq Subtype.val _ _ (fun u v => Iff.rfl) ?_ ?_
    · intro u
      simp only [true_iff]
      rintro ⟨x, hx, hxl⟩
      exact u.2 ⟨x, hxl, (Quotient.exact hx).symm⟩
    · intro q hq
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      refine ⟨⟨x, ?_⟩, rfl⟩
      rintro ⟨y, hy, hxy⟩
      exact hq ⟨y, Quotient.sound hxy.symm, hy⟩
  -- the whole map
  have h4 : cycleCount G.face
      = Nat.card {q : Quotient (SameCycle.setoid G.face) // Meets _ (· ∈ Set.range hr) q}
        + Nat.card {q : Quotient (SameCycle.setoid G.face) // ¬ Meets _ (· ∈ Set.range hr) q} :=
    card_split _
  have h5 : cycleCount Gr.face
      = Nat.card {q : Quotient (SameCycle.setoid G.face) // Meets _ (· ∈ Set.range hr) q} := by
    change Nat.card (Quotient (SameCycle.setoid Gr.face)) = _
    rw [← card_subtype_true]
    refine card_quotient_eq hr _ _ (P.cface_hr_iff) ?_ ?_
    · intro y
      simp only [true_iff]
      exact ⟨hr y, rfl, ⟨y, rfl⟩⟩
    · intro q hq
      obtain ⟨z, hz, y, rfl⟩ := hq
      exact ⟨y, hz⟩
  have h6 : Nat.card (Quotient S)
      = Nat.card {q : Quotient (SameCycle.setoid G.face) // ¬ Meets _ (· ∈ Set.range hr) q} := by
    rw [← card_subtype_true]
    refine card_quotient_eq (fun u : {xd : Dd // Gd.Kernel bd xd} => hd u.val) _ _ ?_ ?_ ?_
    · intro u v
      exact P.cface_hd_iff (fun hout => u.2 ((P.mem_outer_hd_iff u.val).mp hout))
    · intro u
      simp only [true_iff]
      rintro ⟨z, hz, y, rfl⟩
      refine u.2 ((P.mem_outer_hd_iff u.val).mp ⟨y, ?_⟩)
      exact (Quotient.exact hz).symm
    · intro q hq
      obtain ⟨z, rfl⟩ := Quotient.exists_rep q
      have hz : z ∉ Set.range hr := fun hm => hq ⟨z, rfl, hm⟩
      obtain ⟨x, rfl⟩ := (P.mem_range_or z).resolve_right hz
      refine ⟨⟨x, ?_⟩, rfl⟩
      intro hb
      obtain ⟨y, hy⟩ := (P.mem_outer_hd_iff x).mpr hb
      exact hq ⟨hr y, Quotient.sound hy.symm, ⟨y, rfl⟩⟩
  omega

/-! #### Cardinalities -/

/-- The disk and the remainder cover `G`, overlapping exactly on the ring. -/
theorem card_patch [Finite D] (P : Patch G Gd Gr hd hr bd br) :
    Nat.card Dd + Nat.card Dr = bd.length + Nat.card D := by
  classical
  have _ : Finite Dd := Finite.of_injective hd P.injd
  have _ : Finite Dr := Finite.of_injective hr P.injr
  have hunion : (Set.range hd ∪ Set.range hr) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact P.mem_range_or x
  have hinter : (Set.range hd ∩ Set.range hr) = {x | x ∈ bd.map hd} := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      rcases (P.range_r x).mp hx2 with h | h
      · exact absurd hx1 h
      · exact h
    · intro hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact ⟨⟨u, rfl⟩, (P.mem_bd_iff u).mpr hu⟩
  have h := Set.ncard_union_add_ncard_inter (Set.range hd) (Set.range hr)
  rw [hunion, hinter, Set.ncard_range_of_injective P.injd,
    Set.ncard_range_of_injective P.injr, Set.ncard_univ] at h
  have hb : ({x | x ∈ bd.map hd} : Set D).ncard = bd.length := by
    have hset : {x | x ∈ bd.map hd} = ((bd.map hd).toFinset : Set D) := by
      ext x; simp
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup P.nodup_ring, List.length_map]
  rw [hb] at h
  omega

/-- The components of the remainder are the components of `G` meeting it. -/
private theorem compCount_r_eq [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) :
    Gr.compCount = Nat.card {q : Quotient G.gcompSetoid // Meets _ (· ∈ Set.range hr) q} := by
  change Nat.card (Quotient Gr.gcompSetoid) = _
  rw [← card_subtype_true]
  refine card_quotient_eq hr _ _ (fun _ _ => eqvGen_glink_hr_iff P) ?_ ?_
  · intro y
    simp only [true_iff]
    exact ⟨hr y, rfl, ⟨y, rfl⟩⟩
  · rintro q ⟨z, hz, y, rfl⟩
    exact ⟨y, hz⟩

/-- The components of the two parts are the components of `G`, plus the one
carrying the ring. -/
private theorem compCount_patch [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) :
    Gd.compCount + Gr.compCount = G.compCount + min bd.length 1 := by
  classical
  have h1 : Gd.compCount
      = Nat.card {p : Quotient Gd.gcompSetoid // Meets _ (· ∈ bd) p}
        + Nat.card {p : Quotient Gd.gcompSetoid // ¬ Meets _ (· ∈ bd) p} := card_split _
  have h4 : G.compCount
      = Nat.card {q : Quotient G.gcompSetoid // Meets _ (· ∈ Set.range hr) q}
        + Nat.card {q : Quotient G.gcompSetoid // ¬ Meets _ (· ∈ Set.range hr) q} :=
    card_split _
  have h5 := compCount_r_eq P
  have h6 : Nat.card {p : Quotient Gd.gcompSetoid // ¬ Meets _ (· ∈ bd) p}
      = Nat.card {q : Quotient G.gcompSetoid // ¬ Meets _ (· ∈ Set.range hr) q} := by
    refine card_quotient_eq hd _ _ (fun _ _ => eqvGen_glink_hd_iff P) ?_ ?_
    · intro xd
      refine not_congr ⟨?_, ?_⟩
      · rintro ⟨zd, hzd, hzb⟩
        exact ⟨hd zd, Quotient.sound (eqvGen_glink_hd P (Quotient.exact hzd)),
          (P.mem_bd_iff zd).mpr hzb⟩
      · rintro ⟨z, hz, yr, rfl⟩
        have hc := diskComp_eqvGen P (Quotient.exact hz)
        rw [diskComp_hr P, diskComp_hd P] at hc
        rcases bd with _ | ⟨w, t⟩
        · simp at hc
        · exact ⟨w, Option.some.inj (by simpa using hc), by simp⟩
    · intro q hq
      obtain ⟨z, rfl⟩ := Quotient.exists_rep q
      have hz : z ∉ Set.range hr := fun hm => hq ⟨z, rfl, hm⟩
      obtain ⟨xd, rfl⟩ := (P.mem_range_or z).resolve_right hz
      exact ⟨xd, rfl⟩
  have h2 : Nat.card {p : Quotient Gd.gcompSetoid // Meets _ (· ∈ bd) p}
      = min bd.length 1 := by
    rcases bd with _ | ⟨z, t⟩
    · rw [card_meets_eq_zero (fun _ => by simp)]
      simp
    · rw [card_meets_eq_one (x₀ := z) (by simp) (fun x hx =>
        eqvGen_glink_of_cedge Gd ((P.cedge_mem_d (by simp) x).mpr hx))]
      simp only [List.length_cons]
      omega
  omega

/-- Cutting a connected map leaves the remainder connected, as long as it has
a dart at all. -/
theorem connected_r [Finite D] [Finite Dd] [Finite Dr] (P : Patch G Gd Gr hd hr bd br)
    (h : G.Connected) (xr : Dr) : Gr.Connected := by
  classical
  have h5 := compCount_r_eq P
  have h4 : G.compCount
      = Nat.card {q : Quotient G.gcompSetoid // Meets _ (· ∈ Set.range hr) q}
        + Nat.card {q : Quotient G.gcompSetoid // ¬ Meets _ (· ∈ Set.range hr) q} :=
    card_split _
  have hpos : 0 < Nat.card {q : Quotient G.gcompSetoid // Meets _ (· ∈ Set.range hr) q} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨Quotient.mk _ (hr xr), ⟨hr xr, rfl, ⟨xr, rfl⟩⟩⟩⟩, inferInstance⟩
  simp only [Hypermap.Connected] at h ⊢
  omega

/-! #### Genus and planarity -/

/-- **The genus of a patch**: cutting a map along a ring splits its genus
between the two pieces. -/
theorem genus_patch [Finite D] (P : Patch G Gd Gr hd hr bd br) :
    G.genus = Gd.genus + Gr.genus := by
  classical
  have hfd : Finite Dd := Finite.of_injective hd P.injd
  have hfr : Finite Dr := Finite.of_injective hr P.injr
  have _ : Fintype D := Fintype.ofFinite D
  have _ : Fintype Dd := Fintype.ofFinite Dd
  have _ : Fintype Dr := Fintype.ofFinite Dr
  have hG := G.evenGenus
  have hGd := Gd.evenGenus
  have hGr := Gr.evenGenus
  simp only [Hypermap.EvenGenus, Hypermap.EulerLhs, Hypermap.EulerRhs] at hG hGd hGr
  have hc := compCount_patch P
  have he := cycleCount_edge_patch P
  have hn := cycleCount_node_patch P
  have hf := cycleCount_face_patch P
  have hcard := P.card_patch
  omega

/-- **Planarity of a patch**: `G` is planar exactly when both parts are. -/
theorem planar_patch [Finite D] (P : Patch G Gd Gr hd hr bd br) :
    G.Planar ↔ Gd.Planar ∧ Gr.Planar := by
  simp only [Hypermap.Planar, genus_patch P]
  omega

/-! #### Plainness and cubicity -/

/-- `G` is plain exactly when the disk is plain off its border and the
remainder is plain. -/
theorem plain_patch [Finite Dd] (P : Patch G Gd Gr hd hr bd br) :
    G.Plain ↔ Gd.PlainOn {xd | xd ∉ bd} ∧ Gr.Plain := by
  constructor
  · intro hG
    refine ⟨⟨fun xd hxd => ?_, fun xd hxd => ?_⟩, ⟨fun xr => ?_, fun xr => ?_⟩⟩
    · have hexd : Gd.edge xd ∉ bd := fun h => hxd ((P.edge_mem_d_iff xd).mp h)
      refine P.injd ?_
      rw [P.edge_d hexd, P.edge_d hxd, hG.edge_edge]
    · intro h
      have h' : G.edge (hd xd) = hd xd := by rw [← P.edge_d hxd, h]
      exact hG.edge_ne (hd xd) h'
    · refine P.injr ?_
      rw [P.edge_r, P.edge_r, hG.edge_edge]
    · intro h
      have h' : G.edge (hr xr) = hr xr := by rw [← P.edge_r, h]
      exact hG.edge_ne (hr xr) h'
  · rintro ⟨hGd, hGr⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · by_cases hxr : x ∈ Set.range hr
      · obtain ⟨xr, rfl⟩ := hxr
        rw [← P.edge_r, ← P.edge_r, hGr.edge_edge]
      · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
        have hxd : xd ∉ bd := fun h => hxr ((P.mem_bd_iff xd).mpr h)
        have hexd : Gd.edge xd ∉ bd := fun h => hxd ((P.edge_mem_d_iff xd).mp h)
        rw [← P.edge_d hxd, ← P.edge_d hexd, hGd.edge_edge xd hxd]
    · by_cases hxr : x ∈ Set.range hr
      · obtain ⟨xr, rfl⟩ := hxr
        rw [← P.edge_r]
        exact fun h => hGr.edge_ne xr (P.injr h)
      · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
        have hxd : xd ∉ bd := fun h => hxr ((P.mem_bd_iff xd).mpr h)
        rw [← P.edge_d hxd]
        exact fun h => hGd.edge_ne xd hxd (P.injd h)

/-- `G` is cubic exactly when the disk is cubic and the remainder is cubic off
its border. -/
theorem cubic_patch [Finite Dr] (P : Patch G Gd Gr hd hr bd br) :
    G.Cubic ↔ Gd.Cubic ∧ Gr.Quasicubic br := by
  constructor
  · intro hG
    refine ⟨⟨fun xd _ => ?_, fun xd _ => ?_⟩, ⟨fun xr hxr => ?_, fun xr hxr => ?_⟩⟩
    · refine P.injd ?_
      rw [P.node_d, P.node_d, P.node_d, hG.node_node_node]
    · intro h
      exact hG.node_ne (hd xd) (by rw [← P.node_d, h])
    · have h1 : Gr.node xr ∉ br := fun h => hxr ((P.node_mem_r_iff xr).mp h)
      have h2 : Gr.node (Gr.node xr) ∉ br := fun h => h1 ((P.node_mem_r_iff _).mp h)
      refine P.injr ?_
      rw [P.node_r h2, P.node_r h1, P.node_r hxr, hG.node_node_node]
    · intro h
      exact hG.node_ne (hr xr) (by rw [← P.node_r hxr, h])
  · rintro ⟨hGd, hGr⟩
    refine ⟨fun x _ => ?_, fun x _ => ?_⟩
    · by_cases hxd : x ∈ Set.range hd
      · obtain ⟨xd, rfl⟩ := hxd
        rw [← P.node_d, ← P.node_d, ← P.node_d, hGd.node_node_node]
      · obtain ⟨xr, rfl⟩ := (P.mem_range_or x).resolve_left hxd
        have hxr : xr ∉ br := fun h => hxd ((P.mem_br_iff xr).mpr h)
        have h1 : Gr.node xr ∉ br := fun h => hxr ((P.node_mem_r_iff xr).mp h)
        have h2 : Gr.node (Gr.node xr) ∉ br := fun h => h1 ((P.node_mem_r_iff _).mp h)
        rw [← P.node_r hxr, ← P.node_r h1, ← P.node_r h2, hGr.node_node_node hxr]
    · by_cases hxd : x ∈ Set.range hd
      · obtain ⟨xd, rfl⟩ := hxd
        rw [← P.node_d]
        exact fun h => hGd.node_ne xd (P.injd h)
      · obtain ⟨xr, rfl⟩ := (P.mem_range_or x).resolve_left hxd
        have hxr : xr ∉ br := fun h => hxd ((P.mem_br_iff xr).mpr h)
        rw [← P.node_r hxr]
        exact fun h => hGr.node_ne hxr (P.injr h)

end Patch

/-! ### Patching a map along an empty ring

Every hypermap is the patch, along empty borders, of the component of any of
its darts and of the complement of that component.  This is the reference
development's first application of patching: it is what shows that a minimal
counter-example to the Four Colour Theorem must be connected. -/

section Gcomp

variable [Finite D] (G : Hypermap D) (z : D)

/-- The component of `z`, as a set of darts. -/
def gcomp (G : Hypermap D) (z : D) : Set D := {x | Relation.EqvGen G.GLink z x}

omit [Finite D] in
theorem mem_gcomp_self : z ∈ gcomp G z := Relation.EqvGen.refl z

omit [Finite D] in
private theorem gcomp_link {x y : D} (h : G.GLink x y) :
    (x ∈ gcomp G z ↔ y ∈ gcomp G z) := by
  constructor
  · exact fun hx => Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ h)
  · exact fun hy => Relation.EqvGen.trans _ _ _ hy (Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ h))

/-- The disk map of a dart: the component of `z`. -/
noncomputable def gcompDisk : Hypermap {x : D // x ∈ gcomp G z} :=
  Hypermap.ofCancel3 (fun u => ⟨G.edge u.1, (gcomp_link G z (G.glink_edge u.1)).mp u.2⟩)
    (fun u => ⟨G.node u.1, (gcomp_link G z (G.glink_node u.1)).mp u.2⟩)
    (fun u => ⟨G.face u.1, (gcomp_link G z (G.glink_face u.1)).mp u.2⟩)
    (fun u => Subtype.ext (G.edgeK u.1))

/-- The remainder map of a dart: the complement of the component of `z`. -/
noncomputable def gcompRem : Hypermap {x : D // x ∉ gcomp G z} :=
  Hypermap.ofCancel3
    (fun u => ⟨G.edge u.1, fun h => u.2 ((gcomp_link G z (G.glink_edge u.1)).mpr h)⟩)
    (fun u => ⟨G.node u.1, fun h => u.2 ((gcomp_link G z (G.glink_node u.1)).mpr h)⟩)
    (fun u => ⟨G.face u.1, fun h => u.2 ((gcomp_link G z (G.glink_face u.1)).mpr h)⟩)
    (fun u => Subtype.ext (G.edgeK u.1))

/-- Every hypermap is patched from the component of any dart and the complement
of that component, along empty borders. -/
theorem patch_gcomp : Patch G (gcompDisk G z) (gcompRem G z)
    (Subtype.val : {x : D // x ∈ gcomp G z} → D)
    (Subtype.val : {x : D // x ∉ gcomp G z} → D) [] [] where
  injd := Subtype.val_injective
  injr := Subtype.val_injective
  scycle_d := ⟨isCyclicChain_nil _, Hypermap.simple_nil⟩
  cycle_r := isCyclicChain_nil _
  nodup_r := List.nodup_nil
  ring := rfl
  range_r x := by
    constructor
    · rintro ⟨u, rfl⟩
      exact Or.inl (by rintro ⟨v, hv⟩; exact u.2 (hv ▸ v.2))
    · rintro (h | h)
      · exact ⟨⟨x, fun hx => h ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩
      · simp at h
  edge_d _ _ := rfl
  node_d _ := rfl
  edge_r _ := rfl
  node_r _ _ := rfl

/-! ### A minimal counter-example is connected -/

/-- A minimal counter-example is connected: otherwise it splits along nothing
into two smaller maps, both of which are colourable by minimality, and their
colourings combine. -/
theorem Hypermap.MinimalCounterExample.connected {D : Type*} [Finite D] {G : Hypermap D}
    (h : G.MinimalCounterExample) : G.Connected := by
  classical
  by_contra hcc
  refine h.noncolorable ?_
  rcases isEmpty_or_nonempty D with hD | hne
  · exact ⟨fun _ => Color.c0, ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩⟩
  obtain ⟨z⟩ := hne
  -- cut `G` into the component of `z` and its complement
  have P := patch_gcomp G z
  have hplanar := P.planar_patch.mp h.planar
  have hbridge := P.bridgeless h.bridgeless
  have hplain := P.plain_patch.mp h.plain
  have hcubic := P.cubic_patch.mp h.cubic
  have hplaind : (gcompDisk G z).Plain := plainOn_univ_iff.mp (by
    have := hplain.1
    simpa using this)
  have hplainr : (gcompRem G z).Plain := hplain.2
  have hcubicd : (gcompDisk G z).Cubic := hcubic.1
  have hcubicr : (gcompRem G z).Cubic := quasicubic_nil_iff.mp hcubic.2
  -- both pieces are strictly smaller
  have _ : Fintype D := Fintype.ofFinite D
  obtain ⟨w, hw⟩ : ∃ w : D, w ∉ gcomp G z := by
    by_contra hall
    push_neg at hall
    refine hcc ?_
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨Quotient.mk _ z⟩⟩
    refine Quotient.inductionOn₂ a b fun u v => Quotient.sound ?_
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall u)) (hall v)
  have hcardd : Nat.card {x : D // x ∈ gcomp G z} < Nat.card D := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt (p := fun x => x ∈ gcomp G z) hw
  have hcardr : Nat.card {x : D // x ∉ gcomp G z} < Nat.card D := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt (p := fun x => x ∉ gcomp G z) (by
      simpa using mem_gcomp_self (G := G) (z := z))
  -- so minimality colours them both
  have hcold := h.minimal (gcompDisk G z)
    ⟨⟨⟨hplanar.1, hbridge.1⟩, hplaind⟩, hcubicd.precubic⟩ hcardd
  have hcolr := h.minimal (gcompRem G z)
    ⟨⟨⟨hplanar.2, hbridge.2⟩, hplainr⟩, hcubicr.precubic⟩ hcardr
  obtain ⟨kd, hkd⟩ := hcold
  obtain ⟨kr, hkr⟩ := hcolr
  refine P.colorable_patch.mpr ⟨[], ⟨kd, hkd, rfl⟩, ⟨kr, hkr, rfl⟩⟩

end Gcomp

end FourColor

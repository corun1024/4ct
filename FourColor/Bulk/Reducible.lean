import FourColor.Bulk.Checks
import FourColor.Bulk.Index
import FourColor.Bulk.Fold
import FourColor.Bulk.Coclosure
import FourColor.CertBase

/-!
# C-reducibility from the bulk checks

The last link: a configuration whose bulk data pass the decidable checks is
C-reducible.  The colourings and the contract colourings are computed by the
kernel from the construction programs (`bulkFinal`); the rank, witness and
choice planes are the certificate.

* `goodCheck` — every rank-zero trace is a colouring up to permutation.
* `contractCheck` — the contract program is valid and every contract
  colouring is certified up to permutation.
* `cfReducible_of_bulkChecks` — **the theorem a generated module applies.**
-/

namespace FourColor
namespace Bulk

open Color

/-- Every rank-zero trace is, up to a colour permutation, a colouring. -/
def goodCheck (m : ℕ) (R : List ℕ) (cp : CProg) : Bool :=
  (zeroMask m R &&& ((2 ^ 3 ^ m - 1) ^^^ permClose m (bulkFinal cp))) == 0

/-- The traces some colour permutation of which is certified (rank zero included). -/
def knownMask (m : ℕ) (R : List ℕ) : ℕ := permClose m (certMask m R)

/-- The contract program is valid and every contract colouring is known. -/
def contractCheck (cf : Config) (m : ℕ) (R : List ℕ) : Bool :=
  match cfctr cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf) with
  | some cpc =>
      validCtrm (cfcontractMask cf) cf.prog &&
        ((bulkFinal cpc &&& ((2 ^ 3 ^ m - 1) ^^^ knownMask m R)) == 0)
  | none => false

/-- Every fold output has the ring length the program prescribes. -/
theorem length_foldList_singleton : ∀ (cp : CProg) (u t : List Color),
    t ∈ foldList cp [u] → t.length = cprsizeFrom cp u.length
  | [], u, t, h => by
      simp only [foldList_nil, List.mem_singleton] at h
      subst h; rfl
  | s :: cp, u, t, h => by
      rw [foldList_cons] at h
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
      obtain ⟨v, hv, ht⟩ := (mem_foldList_iff cp _ t).mp h
      rw [length_foldList_singleton cp v t ht, length_enum1 s u v hv]
      rfl

theorem length_finalTraces (rp : CProg) : ∀ t ∈ finalTraces rp, t.length = cprsizeFrom rp 2 := by
  intro t ht
  match rp, ht with
  | .R _ :: cp, ht => exact length_finalTraces cp t ht
  | .Y :: cp, ht =>
      simp only [finalTraces] at ht
      exact length_foldList_singleton cp _ t ht
  | .U :: cp, ht =>
      simp only [finalTraces, List.mem_append] at ht
      rcases ht with ht | ht <;> exact length_foldList_singleton cp _ t ht
  | [], ht => exact length_foldList_singleton [] _ t ht
  | .R' :: cp, ht => exact length_foldList_singleton (.R' :: cp) _ t ht
  | .H :: cp, ht => exact length_foldList_singleton (.H :: cp) _ t ht
  | .K :: cp, ht => exact length_foldList_singleton (.K :: cp) _ t ht
  | .A :: cp, ht => exact length_foldList_singleton (.A :: cp) _ t ht

theorem length_of_mem_finalTraces {cp : CProg} {t : List Color} (ht : t ∈ finalTraces cp.reverse) :
    t.length = cprsize cp := by
  rw [cprsize_eq_cprsizeFrom]
  exact length_finalTraces _ t ht

/-- The co-closure is stable under colour permutations, forwards. -/
theorem kempeCoclosure_map {P : List Color → Prop} {et : List Color} (g : EdgePerm)
    (h : KempeCoclosure P et) : KempeCoclosure P (et.map g) := by
  apply kempeCoclosure_of_map g⁻¹
  rw [List.map_map]
  have : (⇑g⁻¹ ∘ ⇑g : Color → Color) = id := by
    funext c; simp
  rw [this, List.map_id]
  exact h

/-- A bulk colouring, up to permutation, is a ring trace of the once-rotated ring. -/
theorem ringTrace_of_permClose_bulkFinal {cp : CProg} {m : ℕ} (hm : cprsize cp = m + 1)
    {j : ℕ} (hj : j < 3 ^ m) (h : (permClose m (bulkFinal cp)).testBit j = true) :
    (cpmap cp).map.RingTrace ((cpmap cp).cpring.rotate 1) (traceOf m j) := by
  obtain ⟨g, hg⟩ := (testBit_permClose m _ j hj).mp h
  have hgj := permIdx_lt g hj
  obtain ⟨t, ht, htail⟩ := (testBit_bulkFinal cp m hm _ hgj).mp hg
  have h0 := zero_notMem_finalTraces _ t ht
  have hmem : Ctree.mem (cpcolor cp) (evenize t.tail) = true := by
    rw [mem_cpcolor_iff]
    exact ⟨evenTrace_evenize _, t, ht, evenPerm t.tail, rfl⟩
  have hring := ringTrace_rot_of_mem_cpcolor hmem
  rw [evenize] at hring
  set e := evenPerm t.tail with he
  rw [map_completeTrace, htail, ← traceOf, traceOf_permIdx, List.map_map] at hring
  have hback := hring.map (e * g)⁻¹
  rw [List.map_map] at hback
  have : ((⇑(e * g)⁻¹ ∘ (⇑e ∘ ⇑g)) : Color → Color) = id := by
    funext c; simp [Function.comp]
  rw [this, List.map_id] at hback
  exact hback

/-- **Known traces are in the co-closure.**  Every trace some colour permutation
of which is certified lies in the Kempe co-closure of the ring traces of the
once-rotated ring. -/
theorem known_coclosure (cf : Config) (m : ℕ) (hcf : cprsize cf.prog = m + 1)
    (R H C : List ℕ) (hlenH : R.length = H.length) (hClen : m < 2 ^ C.length)
    (hH : H = minPerm m R) (hgood : goodCheck m R cf.prog = true)
    (hchoice : choiceCheck m R C = true) (hpairs : allPairs m R H C = true) :
    ∀ j, j < 3 ^ m → (knownMask m R).testBit j = true →
      KempeCoclosure ((cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1)) (traceOf m j) := by
  set P₀ := (cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1) with hP₀
  set goodAll := permClose m (bulkFinal cf.prog) with hgoodAll
  have hgood' : zeroMask m R &&& ((2 ^ 3 ^ m - 1) ^^^ goodAll) = 0 := by
    simpa [goodCheck] using hgood
  have hgoodPerm : ∀ (g : EdgePerm) (j : ℕ), j < 3 ^ m →
      goodAll.testBit (permIdx g m j) = goodAll.testBit j :=
    fun g j hj => permClose_permIdx m _ g j hj
  have hcert := hcert_of_bulk hlenH hH hClen hgood' hgoodPerm (choiceCheck_spec₁ hchoice)
    (choiceCheck_spec₂ hClen hchoice) (fun p q hpq hq => allPairs_spec hpairs p q hpq hq)
  -- colourings are in the co-closure, and so is every certified trace
  have hPgood : ∀ et, PGood m goodAll et → KempeCoclosure P₀ et := by
    rintro et ⟨j, hj, hgj, rfl⟩
    exact kempeCoclosure_of_mem (ringTrace_of_permClose_bulkFinal hcf hj hgj)
  have hS : ∀ et, SCert m R et → KempeCoclosure P₀ et := fun et hSet =>
    kempeCoclosure_trans hPgood
      (kempeCoclosure_of_rank (P := PGood m goodAll) (S := SCert m R) (rankOf m R) hcert hSet)
  intro j hj hk
  obtain ⟨g, hg⟩ := (testBit_permClose m _ j hj).mp hk
  have hgj := permIdx_lt g hj
  rw [testBit_certMask R hgj] at hg
  simp only [decide_eq_true_eq] at hg
  have hco : KempeCoclosure P₀ (traceOf m (permIdx g m j)) := by
    by_cases hz : val R (permIdx g m j) = 0
    · apply hPgood
      refine ⟨_, hgj, ?_, rfl⟩
      have hzb : (zeroMask m R).testBit (permIdx g m j) = true := by
        rw [testBit_zeroMask R hgj]; simp [hz]
      have := congrArg (fun x => x.testBit (permIdx g m j)) hgood'
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
        hzb, hgj, decide_true, Bool.true_and, Bool.true_xor] at this
      cases h : goodAll.testBit (permIdx g m j)
      · rw [h] at this; exact absurd this (by simp)
      · rfl
    · exact hS _ ⟨_, hgj, by omega, hg, rfl⟩
  rw [traceOf_permIdx] at hco
  exact kempeCoclosure_of_map g hco

/-- The contract program and its validity, read off `contractCheck`. -/
theorem contractCtree_of_check {cf : Config} {cpc : CProg}
    (hcpc : cfctr cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf) = some cpc)
    (hvalid : validCtrm (cfcontractMask cf) cf.prog = true) :
    contractCtree cf = some (cpcolor cpc) := by
  rw [contractCtree, hcpc]; simp [hvalid]

/-- A contract-tree member, located in the bulk universe: it is a colour
permutation of `traceOf m j` for a bit `j` of the contract program's bulk mask. -/
theorem contract_mem_bulk {cpc : CProg} {m : ℕ} (hsize : cprsize cpc = m + 1) {es : List Color}
    (hes : Ctree.mem (cpcolor cpc) (evenize es) = true) :
    ∃ j, j < 3 ^ m ∧ (bulkFinal cpc).testBit j = true ∧
      ∃ g : EdgePerm, completeTrace es = (traceOf m j).map g := by
  rw [mem_cpcolor_iff] at hes
  obtain ⟨-, t, ht, g, hv⟩ := hes
  have h0 := zero_notMem_finalTraces _ t ht
  have h0t : (0 : Color) ∉ t.tail := fun h => h0 (List.mem_of_mem_tail h)
  have hlen : t.tail.length = m := by
    have := length_of_mem_finalTraces ht
    rw [List.length_tail, this, hsize]; rfl
  set j := indexOf m t.tail with hj
  have hpart : partialOf m j = t.tail := partialOf_indexOf hlen h0t
  refine ⟨j, indexOf_lt m _, ?_, evenPerm es * g, ?_⟩
  · exact (testBit_bulkFinal cpc m hsize _ (indexOf_lt m _)).mpr ⟨t, ht, hpart.symm⟩
  · have hrec : completeTrace es = (completeTrace (evenize es)).map (evenPerm es) := by
      rw [← map_completeTrace, map_evenize_evenPerm']
    have htr : completeTrace (partialOf m j) = traceOf m j := rfl
    rw [hrec, hv, map_completeTrace, ← hpart, htr, List.map_map]
    apply List.map_congr_left
    intro c _
    simp

/-- **C-reducibility from the bulk checks.** -/
theorem cfReducible_of_bulkChecks (cf : Config) (m : ℕ) (hcf : cprsize cf.prog = m + 1)
    (R H C : List ℕ) (hlenH : R.length = H.length) (hClen : m < 2 ^ C.length)
    (hH : H = minPerm m R) (hgood : goodCheck m R cf.prog = true)
    (hchoice : choiceCheck m R C = true) (hpairs : allPairs m R H C = true)
    (hctr : contractCheck cf m R = true) : CfReducible cf := by
  have hknown := known_coclosure cf m hcf R H C hlenH hClen hH hgood hchoice hpairs
  unfold contractCheck at hctr
  cases hcpc : cfctr cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf) with
  | none => rw [hcpc] at hctr; exact absurd hctr (by simp)
  | some cpc =>
    rw [hcpc] at hctr
    simp only [Bool.and_eq_true, beq_iff_eq] at hctr
    obtain ⟨hvalid, hcov⟩ := hctr
    have hcc := contractCtree_of_check hcpc hvalid
    obtain ⟨cpc', hcpc', hsize, -⟩ := exists_cfctr_of_contractCtree hcc
    rw [hcpc] at hcpc'
    obtain rfl := Option.some.inj hcpc'
    have hsize' : cprsize cpc = m + 1 := by rw [hsize, hcf]
    refine cfReducible_of_coclosure hcc ?_
    intro es hes
    obtain ⟨j, hjlt, hbit, g, hg⟩ := contract_mem_bulk hsize' hes
    have hkn : (knownMask m R).testBit j = true := by
      have := congrArg (fun x => x.testBit j) hcov
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
        hbit, hjlt, decide_true, Bool.true_and, Bool.true_xor] at this
      cases h : (knownMask m R).testBit j
      · rw [h] at this; exact absurd this (by simp)
      · rfl
    rw [hg]
    exact kempeCoclosure_map g (hknown j hjlt hkn)

end Bulk
end FourColor

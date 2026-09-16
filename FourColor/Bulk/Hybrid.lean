import FourColor.Bulk.Reducible
import FourColor.Bulk.Small
import FourColor.MaskWit

/-!
# C-reducibility from a bulk certificate and a residual walk

For the configurations the bulk rule does not settle on its own, the leftover
contract colourings are certified by the mask walk of `FourColor.MaskCert`
over a small universe, whose "free" witnesses are the traces the bulk stage
already knows.  This file assembles the two:

* `freeCheck` — every free witness of the residual certificate is a known
  trace of the bulk certificate;
* `resCheck` — the residual entries, mapped into the bulk universe;
* `contractCheckH` — every contract colouring is known or a residual entry,
  up to a colour permutation;
* `cfReducible_of_hybrid` — **the theorem a generated residual module applies.**
-/

namespace FourColor
namespace Bulk

open Color

/-- The number of pieces covering the bulk universe. -/
def pieceCount (m : ℕ) : ℕ := 3 ^ m / pieceBits + 1

theorem lt_pieceCount_mul {m i : ℕ} (hi : i < 3 ^ m) : i < pieceCount m * pieceBits := by
  unfold pieceCount
  have := Nat.div_add_mod (3 ^ m) pieceBits
  have := Nat.mod_lt (3 ^ m) (show 0 < pieceBits by decide)
  nlinarith

/-- Every free witness of the residual certificate is known in the bulk sense. -/
def freeCheck (ms : Masks) (m : ℕ) (known goodMask : ℕ) (lo n : ℕ) : Bool :=
  let P := pieces known (pieceCount m)
  (List.range' lo n).all fun j =>
    !goodMask.testBit j || (memPiece P (bigOf ms m j) && lastOk ms m j)

/-- The residual entries, each with its bulk index. -/
def resCheck (ms : Masks) (m : ℕ) (certMask : ℕ) (E : List (ℕ × ℕ)) : Bool :=
  E.all fun e => decide (e.1 < ms.width) && certMask.testBit e.1 &&
    (bigOf ms m e.1 == e.2) && lastOk ms m e.1

/-- The offsets of the entries' bulk indices, one list per piece. -/
def resPieces (E : List (ℕ × ℕ)) (k : ℕ) : List (List ℕ) :=
  (List.range k).map fun c => (E.filter fun e => e.2 / pieceBits == c).map fun e => e.2 % pieceBits

/-- Every contract colouring is known, or a residual entry, up to permutation. -/
def contractCheckH (cf : Config) (m : ℕ) (R : List ℕ) (resMask : ℕ) : Bool :=
  match cfctr cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf) with
  | some cpc =>
      validCtrm (cfcontractMask cf) cf.prog &&
        ((bulkFinal cpc &&& ((2 ^ 3 ^ m - 1) ^^^ (knownMask m R ||| permClose m resMask))) == 0)
  | none => false

theorem mem_of_testBit_buildMask_resPieces {E : List (ℕ × ℕ)} {k i : ℕ}
    (hi : i < k * pieceBits) (h : (buildMask (resPieces E k)).testBit i = true) :
    ∃ e ∈ E, e.2 = i := by
  have hL : ∀ ks ∈ resPieces E k, ∀ x ∈ ks, x < pieceBits := by
    intro ks hks x hx
    unfold resPieces at hks
    rw [List.mem_map] at hks
    obtain ⟨c, -, rfl⟩ := hks
    rw [List.mem_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    exact Nat.mod_lt _ (by decide)
  have hpos : 0 < pieceBits := by decide
  have hdecomp : i = i / pieceBits * pieceBits + i % pieceBits := (Nat.div_add_mod' i pieceBits).symm
  rw [hdecomp, testBit_buildMask _ hL _ _ (Nat.mod_lt _ hpos)] at h
  rw [decide_eq_true_eq] at h
  have hc : i / pieceBits < k := by rw [Nat.div_lt_iff_lt_mul hpos]; exact hi
  unfold resPieces at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc] at h
  simp only [Option.map_some, Option.getD_some, List.mem_map, List.mem_filter,
    beq_iff_eq] at h
  obtain ⟨e, ⟨he, hec⟩, hoff⟩ := h
  refine ⟨e, he, ?_⟩
  rw [hdecomp, ← hec, ← hoff, Nat.div_add_mod']

/-- **C-reducibility from the bulk certificate and the residual walk.** -/
theorem cfReducible_of_hybrid (cf : Config) (m : ℕ) (hcf : cprsize cf.prog = m + 1)
    (R H C : List ℕ) (hlenH : R.length = H.length) (hClen : m < 2 ^ C.length)
    (hH : H = minPerm m R) (hgood : goodCheck m R cf.prog = true)
    (hchoice : choiceCheck m R C = true) (hpairs : allPairs m R H C = true)
    -- the residual walk
    (ms : Masks) (hlen : ms.len = m + 1) (hchk : ms.consistentCheck = true)
    (certMask goodMask : ℕ) (wl : List (ℕ × List (EdgePerm × ℕ)))
    (rps : RankPairs) (hrps : rps = Masks.buildRank goodMask wl)
    (hpw : ∀ ent ∈ wl, ∀ gm ∈ ent.2,
      ms.pairWalk gm.1 (fun b => b &&& (certMask &&& ent.1 &&& ms.full) != 0)
        (List.range ms.len) gm.2 ms.full = true)
    (hlwchk : rps.all (fun q => q.2 &&& ms.full == q.2) = true)
    (hwalk : ms.walk (Masks.leafTest certMask rps) (List.range ms.len) [] ms.full = true)
    (chunk nch : ℕ) (hchunk : 0 < chunk) (hcov : ms.width ≤ nch * chunk)
    (hfree : ∀ k, k < nch → freeCheck ms m (knownMask m R) goodMask (k * chunk) chunk = true)
    (E : List (ℕ × ℕ)) (hE : resCheck ms m certMask E = true)
    (hctr : contractCheckH cf m R (buildMask (resPieces E (pieceCount m))) = true) :
    CfReducible cf := by
  set P₀ := (cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1) with hP₀
  have hknown := known_coclosure cf m hcf R H C hlenH hClen hH hgood hchoice hpairs
  have hc : ms.Consistent := ms.consistent_of_check hchk
  -- free witnesses are in the co-closure
  have hgoodP : ∀ j, j < ms.width → goodMask.testBit j = true → KempeCoclosure P₀ (ms.traceOf j) := by
    intro j hj hgj
    have hk : j / chunk < nch := by
      rw [Nat.div_lt_iff_lt_mul hchunk]; omega
    have h := hfree (j / chunk) hk
    unfold freeCheck at h
    rw [List.all_eq_true] at h
    have hmem : j ∈ List.range' (j / chunk * chunk) chunk := by
      rw [List.mem_range'_1]
      have := Nat.div_add_mod j chunk
      have := Nat.mod_lt j hchunk
      constructor <;> nlinarith [Nat.div_mul_le_self j chunk]
    have := h j hmem
    simp only [hgj, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    obtain ⟨hmem, hlast⟩ := this
    rw [memPiece_pieces _ _ _ (lt_pieceCount_mul (bigOf_lt ms m j))] at hmem
    rw [← traceOf_bigOf ms hc hlen hj hlast]
    exact hknown _ (bigOf_lt ms m j) hmem
  -- the residual walk certifies its traces, with the co-closure as the base predicate
  have hlw := ms.hlw_of_check rps hlwchk
  have hwit := ms.hwit_of_buildRank certMask goodMask (P := KempeCoclosure P₀) wl hgoodP
    (fun ent hent gm hgm i hi hb =>
      ms.atLevel_of_pairWalk hc gm.1 certMask ent.1 gm.2 (hpw ent hent gm hgm) i hi hb)
  rw [← hrps] at hwit
  have hco := ms.coclosure_of_walk hc certMask rps hlw hwit hwalk (fun _ hi => ms.testBit_full hi)
  have hres : ∀ et, ms.Cert certMask et → KempeCoclosure P₀ et := fun et h =>
    kempeCoclosure_trans (fun _ h' => h') (hco et h)
  -- the contract
  unfold contractCheckH at hctr
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
    have hkn : (knownMask m R ||| permClose m (buildMask (resPieces E (pieceCount m)))).testBit j
        = true := by
      have := congrArg (fun x => x.testBit j) hcov
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
        hbit, hjlt, decide_true, Bool.true_and, Bool.true_xor] at this
      cases h : (knownMask m R ||| permClose m (buildMask (resPieces E (pieceCount m)))).testBit j
      · rw [h] at this; exact absurd this (by simp)
      · rfl
    rw [Nat.testBit_or, Bool.or_eq_true] at hkn
    rw [hg]
    apply kempeCoclosure_map g
    rcases hkn with hkn | hkn
    · exact hknown j hjlt hkn
    · -- a residual entry, up to permutation
      obtain ⟨g', hg'⟩ := (testBit_permClose m _ j hjlt).mp hkn
      have hgj := permIdx_lt g' hjlt
      obtain ⟨e, heE, hej⟩ := mem_of_testBit_buildMask_resPieces (lt_pieceCount_mul hgj) hg'
      unfold resCheck at hE
      rw [List.all_eq_true] at hE
      have := hE e heE
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      obtain ⟨⟨⟨hew, hecert⟩, hebig⟩, helast⟩ := this
      have hco' : KempeCoclosure P₀ (traceOf m (permIdx g' m j)) := by
        rw [← hej, ← hebig, traceOf_bigOf ms hc hlen hew helast]
        exact hres _ ⟨e.1, hew, hecert, rfl⟩
      rw [traceOf_permIdx] at hco'
      exact kempeCoclosure_of_map g' hco'


/-! ### Splitting the checks across declarations -/

theorem freeCheck_append (ms : Masks) (m known goodMask lo n₁ n₂ : ℕ) :
    freeCheck ms m known goodMask lo (n₁ + n₂) =
      (freeCheck ms m known goodMask lo n₁ && freeCheck ms m known goodMask (lo + n₁) n₂) := by
  unfold freeCheck
  rw [← List.range'_append_1, List.all_append]

theorem resCheck_append (ms : Masks) (m certMask : ℕ) (E₁ E₂ : List (ℕ × ℕ)) :
    resCheck ms m certMask (E₁ ++ E₂) = (resCheck ms m certMask E₁ && resCheck ms m certMask E₂) := by
  unfold resCheck
  rw [List.all_append]

/-- Residual entries packed forty bits each (`j` in the low eighteen, the bulk
index above), unpacked from a numeral. -/
def unpackE (N : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | t + 1 =>
    let w := (N >>> (40 * t)) &&& (2 ^ 40 - 1)
    (w &&& (2 ^ 18 - 1), w >>> 18) :: unpackE N t

end Bulk
end FourColor

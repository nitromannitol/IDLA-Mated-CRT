import MatedCRT.FirstPass.Derived.BlockDegreeGoodEvent
import MatedCRT.FirstPass.Derived.BlockDegreeExponents
import MatedCRT.FirstPass.Derived.DegreeLemmaA5OfBlocks
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.External.SLE

/-!
# The block degree estimate from the running-minimum tail

Berestycki–Gwynne (2020), Appendix A, proves (A.43): with polynomially high probability, every block of
`N = ⌊ε^{-1/2}⌋` consecutive cells whose union meets `B_ρ` has degree sum within `ε^{-1/2 + κ}` of `6N`.
The deterministic part is `MatedCRTEnv.abs_sum_matedDeg_block_sub_le_of_runningMin_le`: on the event that
the cells are small, the curve covers the unit disk in a bounded time window, the degrees are at most
`log² ε⁻¹`, the cell minima of the boundary-length paths are distinct and the running-minimum count of every
relevant block is at most `4 m` with `m = ε^{-1/4} log² ε⁻¹`, the block degree sum is within
`2 + (2 + log² ε⁻¹) 4 m ≤ ε^{-1/2 + 1/8}` of `6N`. This file supplies the probability bounds.

The two Brownian inputs are explicit hypotheses, stated for every law `μ` on `Path2 = C(ℝ, ℝ × ℝ)` with the
correlated Brownian law `IsCorrelatedBM2 γ μ`:
* `hF4`: almost surely the cell minima of each coordinate are distinct;
* `hF6` (BG20 Lemma A.9, after Brownian scaling): the number of cells of a block of `N` cells containing a
  running minimum of a coordinate, or of its time reversal on the block, exceeds `m` with probability at most
  `C exp(-c m / √N)`.

## Main results
* `MatedCRTEnv.IsValid.polyHighProb_blockRunningMin`: with polynomially high probability the cell minima are
  distinct and every block with index in `blockIndexRange (N ε) ε⁻¹` has running-minimum count at most `4 m`
  (a union bound over at most `4 ε^{-2}` blocks, each failing with probability `≤ 4 C exp(-c log² ε⁻¹)`);
* `hblock_of_runningMinTail`: the hypothesis `hblock` of `lemmaA5_of_blockDegree`, with `κ = 1/8`, from the
  cell size estimate, the degree bound, `hF4` and `hF6`.
-/

open Set Metric MeasureTheory Filter HarmonicBalls MatedCRTHarmonic.MatedCRT
open scoped Finset

namespace MatedCRT

/-- **The running-minimum event of the blocks.** For a valid environment, if the cell minima of each
coordinate of a correlated Brownian path are almost surely distinct (`hF4`) and the running-minimum counts of
a block of `N` cells have the tail `C exp(-c m / √N)` (`hF6`), then with polynomially high probability the
cell minima of `L` and `R` are distinct and every block `j ∈ blockIndexRange (N ε) ε⁻¹`, `N = ⌊ε^{-1/2}⌋`,
has running-minimum count at most `4 ε^{-1/4} log² ε⁻¹`. -/
theorem MatedCRTEnv.IsValid.polyHighProb_blockRunningMin {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hF4 : ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ ε : ℝ, 0 < ε →
      ∀ᵐ p ∂μ, ∀ i : Fin 2, Function.Injective (bmCellMin ε fun t => lrCoord i t p))
    {C c : ℝ} (hc : 0 < c)
    (hF6 : ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ (i : Fin 2) (ε : ℝ), 0 < ε →
      ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
        μ {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(blockRunningMinCells ε
          (blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N)))) :
    PolyHighProb S.P fun ε => {ω |
      Function.Injective (bmCellMin ε fun t => (S.bm ω t).1) ∧
      Function.Injective (bmCellMin ε fun t => (S.bm ω t).2) ∧
      ∀ j ∈ blockIndexRange ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ε⁻¹,
        (blockRunningMinCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
          ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1) + 1)
          ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1) + ⌊ε ^ (-(1 / 2 : ℝ))⌋₊) : ℝ) ≤
          4 * (ε ^ (-(1 / 4 : ℝ)) * Real.log ε⁻¹ ^ 2)} := by
  obtain ⟨hlaw, hmeas⟩ := hS.isCorrelatedBM2_map_bm
  obtain ⟨ε₄, hε₄, hsmall⟩ := exists_mul_rpow_neg_mul_exp_le (16 * max C 0) c 2 hc
  refine ⟨1, one_pos, 1, min 1 ε₄, lt_min one_pos hε₄, fun ε hε hεε => ?_⟩
  have hε1 : ε < 1 := hεε.trans_le (min_le_left _ _)
  obtain ⟨hn1, hnp, -, -, -⟩ := floor_rpow_neg_half_bounds hε hε1
  set N : ℕ := ⌊ε ^ (-(1 / 2 : ℝ))⌋₊ with hN
  set L : ℝ := Real.log ε⁻¹ with hL
  set m : ℝ := ε ^ (-(1 / 4 : ℝ)) * L ^ 2 with hm
  set y : ℝ := 4 * max C 0 * Real.exp (-(c * L ^ 2)) with hy
  have hC0 : 0 ≤ max C 0 := le_max_right C 0
  have hy0 : 0 ≤ y := by positivity
  -- the cell minima are distinct almost surely
  have hinj : S.P {ω | ¬ (Function.Injective (bmCellMin ε fun t => (S.bm ω t).1) ∧
      Function.Injective (bmCellMin ε fun t => (S.bm ω t).2))} = 0 := by
    refine ae_iff.1 ?_
    filter_upwards [ae_of_ae_map hmeas.aemeasurable (hF4 _ hlaw ε hε)] with ω h
    exact ⟨by simpa only [lrCoord_zero_apply] using h 0, by simpa only [lrCoord_one_apply] using h 1⟩
  -- the tail of one block
  have hsqrt : Real.sqrt N ≤ ε ^ (-(1 / 4 : ℝ)) := by
    calc Real.sqrt N ≤ Real.sqrt (ε ^ (-(1 / 2 : ℝ))) := Real.sqrt_le_sqrt hnp
      _ = ε ^ (-(1 / 4 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]
        norm_num
  have hNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hmN : c * L ^ 2 ≤ c * m / Real.sqrt N := by
    rw [le_div_iff₀ hNpos]
    calc c * L ^ 2 * Real.sqrt N ≤ c * L ^ 2 * ε ^ (-(1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = c * m := by rw [hm]; ring
  have hblk : ∀ j ∈ blockIndexRange ((N : ℝ) * ε) ε⁻¹,
      S.P {ω | 4 * m < (blockRunningMinCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
        ((N : ℤ) * (j - 1) + 1) ((N : ℤ) * (j - 1) + N) : ℝ)} ≤ ENNReal.ofReal y := by
    intro j _
    refine (hS.measure_lt_blockRunningMinCount_le fun μ hμ i =>
      hF6 μ hμ i ε hε _ N (by exact_mod_cast hn1) m).trans ?_
    rw [show (4 : ENNReal) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp := Real.exp_le_exp.2 (neg_le_neg hmN)
    calc 4 * (C * Real.exp (-(c * m / Real.sqrt N)))
        ≤ 4 * (max C 0 * Real.exp (-(c * m / Real.sqrt N))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le) (by norm_num)
      _ ≤ 4 * (max C 0 * Real.exp (-(c * L ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hC0) (by norm_num)
      _ = y := by rw [hy]; ring
  -- the union bound over the block index range
  have hU : S.P (⋃ j ∈ blockIndexRange ((N : ℝ) * ε) ε⁻¹,
      {ω | 4 * m < (blockRunningMinCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
        ((N : ℤ) * (j - 1) + 1) ((N : ℤ) * (j - 1) + N) : ℝ)}) ≤
      ENNReal.ofReal ((#(blockIndexRange ((N : ℝ) * ε) ε⁻¹) : ℝ) * y) := by
    refine (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hblk).trans ?_)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, nsmul_eq_mul]
  have hδ : 0 < (N : ℝ) * ε := mul_pos (by linarith) hε
  have hinv1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1.le
  have hcard : (#(blockIndexRange ((N : ℝ) * ε) ε⁻¹) : ℝ) ≤ 4 * (ε⁻¹ * ε⁻¹) := by
    have h1 := card_blockIndexRange_le hδ (inv_nonneg.2 hε.le)
    have h2 : 2 * ε⁻¹ / ((N : ℝ) * ε) ≤ 2 * ε⁻¹ / ε :=
      div_le_div_of_nonneg_left (by positivity) hε (le_mul_of_one_le_left hε.le hn1)
    rw [div_eq_mul_inv (2 * ε⁻¹) ε] at h2
    nlinarith
  have hreal : (#(blockIndexRange ((N : ℝ) * ε) ε⁻¹) : ℝ) * y ≤ 1 * ε ^ (1 : ℝ) := by
    have h := hsmall ε hε (hεε.trans_le (min_le_right _ _))
    rw [Real.rpow_neg hε.le, Real.rpow_two, sq, mul_inv] at h
    rw [one_mul, Real.rpow_one]
    calc (#(blockIndexRange ((N : ℝ) * ε) ε⁻¹) : ℝ) * y ≤ 4 * (ε⁻¹ * ε⁻¹) * y :=
          mul_le_mul_of_nonneg_right hcard hy0
      _ = 16 * max C 0 * (ε⁻¹ * ε⁻¹) * Real.exp (-(c * Real.log ε⁻¹ ^ 2)) := by rw [hy]; ring
      _ ≤ ε := h
  calc S.P _ ≤ S.P ({ω | ¬ (Function.Injective (bmCellMin ε fun t => (S.bm ω t).1) ∧
        Function.Injective (bmCellMin ε fun t => (S.bm ω t).2))} ∪
        ⋃ j ∈ blockIndexRange ((N : ℝ) * ε) ε⁻¹,
          {ω | 4 * m < (blockRunningMinCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
            ((N : ℤ) * (j - 1) + 1) ((N : ℤ) * (j - 1) + N) : ℝ)}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hne
        simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hne
        obtain ⟨h1, h2⟩ := hne
        exact hω ⟨(not_not.1 h1).1, (not_not.1 h1).2, fun j hj => not_lt.1 (h2 j hj)⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal ((#(blockIndexRange ((N : ℝ) * ε) ε⁻¹) : ℝ) * y) :=
        add_le_add hinj.le hU
    _ ≤ ENNReal.ofReal (1 * ε ^ (1 : ℝ)) := by
        rw [zero_add]
        exact ENNReal.ofReal_le_ofReal hreal

/-- **The block degree estimate (BG20 (A.43)) from the running-minimum tail.** Given the cell size
estimate (Lemma 2.8), the degree bound `DegreeBoundInput`, almost sure distinctness of the cell minima of
each coordinate of a correlated Brownian path (`hF4`) and the tail `C exp(-c m / √N)` of the number of cells
of a block of `N` cells containing a running minimum of a coordinate or of its reversal on the block
(`hF6`, BG20 Lemma A.9), with polynomially high probability every block of `N = ⌊ε^{-1/2}⌋` cells meeting
`B_ρ` has degree sum within `ε^{-1/2 + 1/8}` of `6N`: this is the hypothesis `hblock` of
`lemmaA5_of_blockDegree`, with `κ = 1/8`. -/
theorem hblock_of_runningMinTail {𝒮 : SpaceFillingSLEModel} (hcell : CellSizeEstimateStmt 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hF4 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ ε : ℝ, 0 < ε →
      ∀ᵐ p ∂μ, ∀ i : Fin 2, Function.Injective (bmCellMin ε fun t => lrCoord i t p))
    (hF6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ C c : ℝ, 0 < c ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ (i : Fin 2) (ε : ℝ), 0 < ε → ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
        μ {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(blockRunningMinCells ε
          (blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N)))) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)} := by
  intro γ hγ hγ2
  obtain ⟨C, c, hc, hF6γ⟩ := hF6 γ hγ hγ2
  refine ⟨1 / 8, by norm_num, fun ρ hρ hρ1 Ω _ S hS => ?_⟩
  set q : ℝ := 1 / (2 + γ) ^ 2 with hq_def
  have hq : 0 < q := by positivity
  have hq1 : q < 1 := by
    rw [hq_def, div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, hae⟩ := hS.matingOfTrees
  obtain ⟨c', hc', C', hcov⟩ := hMoT.coverage
  have hcovP : PolyHighProb S.P fun ε => {ω | ball (0 : ℂ) 1 ⊆ η' ω '' Set.Icc (-ε⁻¹) ε⁻¹} := by
    refine ⟨c', hc', C', 1, one_pos, fun ε hε hε1 => ?_⟩
    have h := hcov _ ((one_lt_inv₀ hε).2 hε1)
    rwa [Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv] at h
  have hφ : ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 < (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε ∧ (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε ≤ ε ^ (1 / 2 : ℝ) := by
    refine ⟨1, one_pos, fun ε hε hε1 => ?_⟩
    obtain ⟨hn1, hnp, -, -, hpε⟩ := floor_rpow_neg_half_bounds hε hε1
    exact ⟨mul_pos (by linarith) hε, (mul_le_mul_of_nonneg_right hnp hε.le).trans_eq hpε⟩
  have hdiamP := polyHighProb_comp_of_le_rpow (hcell γ hγ hγ2 q ρ hq hq1 hρ hρ1 Ω S hS)
    (by norm_num : (0 : ℝ) < 1 / 2) hφ
  have hρ'0 : 0 < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  have hdegP := hdeg γ hγ hγ2 ((1 + ρ) / 2) hρ'0 hρ'1 Ω S hS
  have hKP := hS.polyHighProb_blockRunningMin (hF4 γ hγ hγ2) hc hF6γ
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | (IsAreaParametrized (S.μ ω) (S.η ω) ∧ ⇑(η' ω) = S.η ω) ∧
      ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω)} :=
    (hS.isAreaParametrized.and (hae.mono fun ω h => h.1)).and
      (hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮))
  obtain ⟨ε₃, hε₃, herr⟩ := exists_blockError_le
  have hs0 : 0 < (1 - ρ) / 2 := by linarith
  have hε₁ : 0 < min (min 1 ε₃) (((1 - ρ) / 2) ^ (2 / q)) :=
    lt_min (lt_min one_pos hε₃) (Real.rpow_pos_of_pos hs0 _)
  refine ((((hdiamP.inter hcovP).inter hdegP).inter hKP).inter_ae hW).mono_of_small hε₁
    fun ε hε hεε ω hω => ?_
  obtain ⟨⟨⟨⟨hdω, hcω⟩, hgω⟩, hinjL, hinjR, hKω⟩, ⟨hpar, hηω⟩, hlf⟩ := hω
  simp only [Set.mem_ofPred_eq] at hdω hcω hgω
  have hε1 : ε < 1 := hεε.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε3 : ε < ε₃ := hεε.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεs : ε < ((1 - ρ) / 2) ^ (2 / q) := hεε.trans_le (min_le_right _ _)
  obtain ⟨hn1, hnp, -, -, hpε⟩ := floor_rpow_neg_half_bounds hε hε1
  have hδ : 0 < (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε := mul_pos (by linarith) hε
  have hδε : (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε ≤ ε ^ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_right hnp hε.le).trans_eq hpε
  have hη : Continuous (S.η ω) := by rw [← hηω]; exact (η' ω).continuous
  rw [hηω] at hcω
  have hsq : ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q < (1 - ρ) / 2 := by
    calc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q ≤ (ε ^ (1 / 2 : ℝ)) ^ q :=
          Real.rpow_le_rpow hδ.le hδε hq.le
      _ = ε ^ (q / 2) := by rw [← Real.rpow_mul hε.le]; congr 1; ring
      _ < (((1 - ρ) / 2) ^ (2 / q)) ^ (q / 2) := Real.rpow_lt_rpow hε.le hεs (by positivity)
      _ = (1 - ρ) / 2 := by
          rw [← Real.rpow_mul hs0.le, show 2 / q * (q / 2) = 1 by field_simp, Real.rpow_one]
  have hs1 : ρ + ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q ≤ (1 + ρ) / 2 := by linarith
  have hs2 : ρ + ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q ≤ 1 := by linarith
  intro j hj
  have hdj : diam (cell ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) (S.η ω) j) ≤
      ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q := by
    have h := (hdω j hj).2
    rwa [hexp] at h
  have hjJ := hpar.mem_blockIndexRange_of_diam_le hη hδ (inv_pos.2 hε) hcω hs2 hj hdj
  exact (S.abs_sum_matedDeg_block_sub_le_of_runningMin_le hε (by exact_mod_cast hn1) hη (hlf ε hε)
    hinjL hinjR hs1 (sq_nonneg (Real.log ε⁻¹)) hgω hj hdj (hKω j hjJ)).trans (herr ε hε hε3)

end MatedCRT

import MatedCRT.FirstPass.Derived.ConeCouplingProd
import MatedCRT.FirstPass.Derived.CellModelProdRight
import MatedCRT.FirstPass.Derived.CoreOfConeCoupling

/-!
# Lemma 2.8 (BG20 Lemma 2.4) without the coupling step

The upper half of the cell size estimate (GMS19 Lemma 2.7, Bonanno's `lemma27_segments`) needs the comparison
`μ_{h̃} ≤ μ_h` on `B_1` of the LQG measure of the quantum cone `h` with that of a whole-plane GFF `h̃` such that
`h = h̃ - γ log |·|` on `B_1` (eq:gff, line 444; DMS14 Definition 4.10). The field `h̃` needs a Brownian motion
independent of `h|_{B_1}` (its radial part outside `B_1`). We take it as the second coordinate of the enlarged sample
space `Ω × C(ℝ≥0, ℝ)` under `P ⊗ BM`, read the cell model of the environment through the first coordinate
(`prodRightCellModel`), prove the comparison there (`areaDominates_prodRight_toCellModel`, from
`exists_coneCoupling_prod` and the deterministic comparison of `Proofs/Sec2/VolumeGrowthHalf/Domination.lean`), and
transfer the conclusion of Lemma 2.7 back to `Ω` (`lemma27_segments_of_prodRight`): its events are preimages under the
first coordinate. Hence:

* `cellSizeUpperStmt_holds`: the upper half of Lemma 2.8 for every space-filling SLE model;
* `cellSizeEstimateStmt_holds`: Lemma 2.8 (lemma:cell-size-estimate, line 669) for every space-filling SLE model,
  the lower half being `cellSizeEstimateStmt_of_volumeGrowth volumeGrowthStmt_holds`;
* `CertifiedReferenceModelCore.of_blockDegree_cellSize`: the core of the reference model without the coupling step.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- **The comparison with a whole-plane GFF on `B_1` for the enlarged cell model.** For a valid environment `S` of a
space-filling SLE model, the cell model of `S` read on `Ω × C(ℝ≥0, ℝ)` under `P ⊗ BM` satisfies
`AreaDominatesWholePlaneGFF`. -/
theorem areaDominates_prodRight_toCellModel {𝒮 : MatedCRT.SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRT.MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    MatedCRTHarmonic.GMSLemma27.AreaDominatesWholePlaneGFF
      (prodRightCellModel (S.toCellModel hS) (brownianMotion 0)) := by
  have hcone := hS.isConeField
  have : IsProbabilityMeasure S.P := hcone.1
  obtain ⟨H, μ', hH, hμ', hrel⟩ := exists_coneCoupling_prod hγ hγ2 hcone.2.1
  refine ⟨H, μ', hH, hμ', ?_⟩
  have hL : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hcone.2.2
  filter_upwards [MatedCRT.isLQGLimit_of_isLQGAreaOf hμ', Measure.quasiMeasurePreserving_fst.ae hL,
    Measure.quasiMeasurePreserving_fst.ae hcone.2.1.ae_continuousOn_circle, hrel]
    with x hμ'x hμx hcont hrelx
  intro A _ hA
  refine MatedCRT.measure_le_of_isLQGLimit_of_le hγ.le hμx hμ'x (fun r hr => ?_) (fun r z hr hz => ?_) hA
  · exact hcont.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hr, mem_univ _⟩
  · rw [hrelx r z hr hz]
    have h0 := MatedCRT.circleAverage_log_norm_nonpos hr.le hz
    have h1 : γ * Real.circleAverage (fun x => Real.log ‖x‖) z r ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inl ⟨hγ.le, h0⟩)
    show H r z x ≤ H r z x - γ * Real.circleAverage (fun x => Real.log ‖x‖) z r
    linarith

/-- **Lemma 2.8, upper half** (GMS19 Lemma 2.7), for every space-filling SLE model. -/
theorem cellSizeUpperStmt_holds (𝒮 : MatedCRT.SpaceFillingSLEModel) : MatedCRT.CellSizeUpperStmt 𝒮 := by
  intro γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω _ S hS
  have hdomM := areaDominates_prodRight_toCellModel hγ hγ2 hS
  have hsq : 0 < (2 + γ) ^ 2 := by positivity
  set q : ℝ := 2 / (2 + γ) ^ 2 - ζ with hq
  set q₀ : ℝ := max q (1 / (2 + γ) ^ 2) with hq₀
  have hq₀0 : 0 < q₀ := lt_max_of_lt_right (by positivity)
  have hq₀' : q₀ < 2 / (2 + γ) ^ 2 :=
    max_lt (by rw [hq]; linarith) ((div_lt_div_iff_of_pos_right hsq).mpr (by norm_num))
  have hα := MatedCRTHarmonic.GMSLemma27.lemma27Exponent_pos hγ hq₀0 hq₀'
  obtain ⟨C, hC⟩ := lemma27_segments_of_prodRight (S.toCellModel hS) (brownianMotion 0)
    (MatedCRT.segmentsContainBalls_toCellModel hS) (MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2) hdomM hγ
    hq₀0 hq₀' hρ hρ1 (half_lt_self hα)
  refine ⟨MatedCRTHarmonic.GMSLemma27.lemma27Exponent q₀ γ / 2, half_pos hα, C, 1, one_pos,
    fun ε hε0 hε1 => le_trans (measure_mono ?_) (hC ε ⟨hε0, hε1⟩)⟩
  refine compl_subset_compl.mpr fun ω hω k hk => ?_
  have h1 : diam (cell ε (S.η ω) k) ≤ ε ^ q₀ := hω _ _ (le_of_eq (by ring)) hk
  exact h1.trans (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (le_max_left _ _))

/-- **Lemma 2.8** (BG20 Lemma 2.4) for every space-filling SLE model: with polynomially high probability as `ε → 0`,
every cell `H^ε_a` which meets `B_ρ` has `ε^{2/(2-γ)² + ζ} ≤ diam(H^ε_a) ≤ ε^{2/(2+γ)² - ζ}`. -/
theorem cellSizeEstimateStmt_holds (𝒮 : MatedCRT.SpaceFillingSLEModel) : MatedCRT.CellSizeEstimateStmt 𝒮 :=
  MatedCRT.cellSizeEstimateStmt_of_volumeGrowth volumeGrowthStmt_holds (cellSizeUpperStmt_holds 𝒮)

/-- **The core of the reference model without the coupling step**: the inputs of
`CertifiedReferenceModelCore.of_coneCoupling_blockDegree` other than `ConeWholePlaneCouplingStep` give the core
(conjunct 5, Lemma 2.8, is `cellSizeEstimateStmt_holds`). -/
theorem CertifiedReferenceModelCore.of_blockDegree_cellSize {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h6 : MatedCRT.CountingMeasureConvergenceStmt 𝒮)
    (h7 : MatedCRT.DegreeMeasureConvergenceStmt 𝒮) (h8 : MatedCRT.FrozenConeScalingLaw 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h17 : MatedCRT.FPSimilarityTransferCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRT.MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)}) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_blockDegree h1 h2 h3 h4 (cellSizeEstimateStmt_holds 𝒮) h6 h7
    h8 h9 h10 h11 h12 h13 h15 h17 h215 hblock

end MatedCRT.FirstPass.Derived

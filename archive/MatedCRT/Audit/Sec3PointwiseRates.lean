import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.DirichletClockTransfer
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.IntegralConvergenceGreenFunctionFinal
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSJointGoodEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.UniformCellSizeMeasurable
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PointwiseEnvelopeMean
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PointwiseEnvelopeTail
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedHarmonicInputs
import MatedCRT.Proofs.Sec1.EnvironmentScaling

/-!
# Section 3 interface consumption checks

This checks interfaces, not the mathematical validity of the cited inputs or
an independent audit of their proofs. The reductions use Leonardo Bonanno's
LatticeProb.Bonanno mated-CRT harmonic-function definitions and results through
the imported modules. Paper locators: corrected draft Lemma 2.8 lines 669–674,
Lemma 3.4 lines 1168–1172, and Lemmas 3.3–3.6. GMS annulus input: arXiv
1807.07511v3, Lemma 3.11 (3.35), p. 31. The stopped-clock convergence and the
rescaled-cone steps are explicit proof obligations, not cited theorems.
-/

namespace MatedCRT.Sec3PointwiseRatesAudit

open MeasureTheory Set Metric Filter Topology MarkovProcess _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The measurable cell event agrees with its geometric version only a.e. -/
theorem cell_event (𝒮 : SpaceFillingSLEModel) (hcell : UniformCellSizeUpperStep 𝒮)
    {γ ρ a : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 0 < a) (ha' : a < 2 / (2 + γ) ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ A : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (A ε)) ∧
        (∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          S.P (A ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
        ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
          (ω ∈ A ε ↔ ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
            diam (cell ε (S.η ω) i) ≤ ε ^ a) :=
  uniform_envSigma_cellSize_of_step 𝒮 hcell hγ hγ2 hρ hρ1 ha ha'

/-- The stopped-clock input is separate from the Green occupation input. -/
theorem stopped_clock {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D U : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ) (F G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hsource : DirichletStoppedClockConvergenceStep P U γ hcirc x G)
    (hD : IsOpen D) (hU : IsOpen U) (hb : Bornology.IsBounded U) (hc : closure U ⊆ D)
    (hx : x ∈ U) (hgff : IsDirichletGFF P D h hcirc)
    (hglobal : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hcirc ω) x (F ω) ∧
      ∀ᵐ b ∂planarBrownianMotion x, IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < lbmExitTime (F ω) U b →
        Tendsto (fun n => b ((killedClockInverse
          (killedGMCClockApprox U γ (hcirc ω) (dyadicScale n) b)
          (ContinuousPath.exitTime U b) t).toNNReal)) atTop
          (𝓝 (liouvilleBrownianPath (F ω) b t)) :=
  berestycki_dirichlet_time_change_eq_lbm P D U h hcirc x γ F G hsource hD hU hb hc hx hgff hglobal

/-- Cone scaling retains the three representation obligations explicitly. -/
theorem cone_scaling (𝒮 : SpaceFillingSLEModel) (hs : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hSc : SLEScaleInvarianceInput 𝒮)
    (hRe : SLEReparametrizationInput 𝒮) (hMo : SLEIndepMonoInput 𝒮)
    (hf : RescaledConeFieldStep 𝒮) (hc : RescaledConeClockStep 𝒮)
    (ht : RescaledMatingOfTreesStep 𝒮) : ConeEnvironmentScalingStep 𝒮 :=
  coneEnvironmentScalingStep_of_inputs 𝒮 hs h22 hSc hRe hMo hf hc ht

/-- The estimate retains its almost-everywhere quantifier. -/
theorem mean_on_envelope
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ ρ' a β p κ : ℝ} (hS : S.IsValid 𝒮 γ)
    (henv : PointwiseCellAnnulusEnvelopeStep S ρ' a β p κ)
    (hm : MepsScalingInput 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hp : 0 < p) (hp1 : p < 1) (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ E : ℝ → Set Ω,
      (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
      (∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        S.P (E ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ κ)) ∧
      ∀ (r : ℝ) (χ : ℝ≥0), 0 < r → 0 < χ →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂S.P, ω ∈ E ε →
          ∀ (z : ℂ) (ψ : ℂ → ℝ) (H : ℝ≥0) (v : ℤ),
            ball z r ⊆ ball 0 ρ → HolderOnWith H χ ψ (closedBall z r) →
            v ∈ interiorCellVertices ε (S.η ω) (ball z r) →
            (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
              C * (H : ℝ) *
                (if (χ : ℝ) < ν then ε ^ (min a β * χ)
                 else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
                 else ε ^ (min a β * ν)) :=
  MatedCRTEnv.IsValid.mean_on_pointwise_cellAnnulus_envelope hS henv hm hγ hγ2 hp hp1 hρ hρρ' ha hβ

/-- The estimate retains its almost-everywhere quantifier. -/
theorem tail_on_envelope
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ ρ' a β p κ : ℝ} (hS : S.IsValid 𝒮 γ)
    (henv : PointwiseCellAnnulusEnvelopeStep S ρ' a β p κ)
    (hm : MepsScalingInput 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hp : 0 < p) (hp1 : p < 1) (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (ha : 0 < a) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ E : ℝ → Set Ω,
      (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
      (∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        S.P (E ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ κ)) ∧
      ∀ (χ : ℝ≥0) (q : ℝ), 0 < χ → 0 < q → q / (χ : ℝ) < min a β →
        ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂S.P, ω ∈ E ε →
          ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
          ∀ (ψ : ℂ → ℝ) (H : ℝ≥0), HolderOnWith H χ ψ (closedBall z r) →
          ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
            srwLaw (S.mult ε ω) v
              {path | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
            ENNReal.ofReal (((2 : ℝ) ^ ν * (202 : ℝ) ^ ν) *
              ε ^ ((min a β - q / (χ : ℝ)) * ν)) :=
  MatedCRTEnv.IsValid.tail_on_pointwise_cellAnnulus_envelope hS henv hm hγ hγ2 hp hp1 hρ hρρ' ha

end MatedCRT.Sec3PointwiseRatesAudit

#print MatedCRT.Sec3PointwiseRatesAudit.cell_event
#print MatedCRT.Sec3PointwiseRatesAudit.stopped_clock
#print MatedCRT.Sec3PointwiseRatesAudit.cone_scaling
#print MatedCRT.MatedCRTEnv.IsValid.mean_on_pointwise_cellAnnulus_envelope
#print MatedCRT.MatedCRTEnv.IsValid.tail_on_pointwise_cellAnnulus_envelope
#print MatedCRT.PointwiseCellAnnulusEnvelopeStep
#print MatedCRT.PointwiseSameWalkRatesStep
#print MatedCRT.AnnealedSameWalkRateStep
#print axioms MatedCRT.Sec3PointwiseRatesAudit.cell_event
#print axioms MatedCRT.Sec3PointwiseRatesAudit.stopped_clock
#print axioms MatedCRT.Sec3PointwiseRatesAudit.cone_scaling
#print axioms MatedCRT.MatedCRTEnv.IsValid.mean_on_pointwise_cellAnnulus_envelope
#print axioms MatedCRT.MatedCRTEnv.IsValid.tail_on_pointwise_cellAnnulus_envelope

#print MatedCRT.Sec3PointwiseRatesAudit.mean_on_envelope
#print MatedCRT.Sec3PointwiseRatesAudit.tail_on_envelope
#print axioms MatedCRT.Sec3PointwiseRatesAudit.mean_on_envelope
#print axioms MatedCRT.Sec3PointwiseRatesAudit.tail_on_envelope

#print MatedCRT.DirichletStoppedClockConvergenceStep
#print MatedCRT.UniformCellSizeUpperStep
#print MatedCRT.LBMGreenOccupationStep
#print MatedCRT.TruncatedDetFixedTimeStep
#print MatedCRT.FiniteDomainDirichletRepresentation
#print MatedCRT.CorrectedHarmonicModulusStep
#print MatedCRT.RescaledConeFieldStep
#print MatedCRT.RescaledConeClockStep
#print MatedCRT.RescaledMatingOfTreesStep

#print MatedCRT.MatedCRTEnv.IsValid.exists_joint_good_event_sameWalk_rates
#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_joint_good_event_sameWalk_rates

#print MatedCRT.GMSAnnulusDisconnectionStmt

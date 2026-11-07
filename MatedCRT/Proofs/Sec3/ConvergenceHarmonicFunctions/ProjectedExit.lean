import MatedCRT.Draft.Section3HarmonicCorrected
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ContinuousPathExit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExitCell

/-! # Projected exit-cell comparison for corrected Lemma 3.6 -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Comparison of expected projected exit-cell data with the expected
unrestricted-walk exit functional. The corrected quantitative argument is in
`LEMMA36-REPLACEMENT.md`, lines 255–335 and 380–404. -/
def CorrectedProjectedExitCellStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, ContinuousOn ψ (closedBall z r) → ∀ y ∈ ball z r,
    TendstoInProbability S.P
      (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y -
        interpolatedExitExpectation S r z y ψ ε ω) (fun _ => 0)

/-- The existing exit-cell comparison applies to projected data whenever the
retracted boundary function is Hölder on a neighbourhood of the disk. -/
theorem correctedProjectedExit_of_holder_retraction (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    {ψ : ℂ → ℝ}
    (hψ : ∃ s : ℝ, 0 < s ∧
      IsHolderContinuousOn (fun x => ψ (ballRetraction z r x)) (closedBall z (r + s)))
    (hy : y ∈ ball z r) :
    TendstoInProbability S.P
      (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y -
        interpolatedExitExpectation S r z y ψ ε ω) (fun _ => 0) := by
  have h := harmonicExitCellStep_of_inputs 𝒮 h211 hmeps hexc hX h28
    γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball
    (fun x => ψ (ballRetraction z r x)) hψ y hy
  have hidem : ∀ x, ballRetraction z r (ballRetraction z r x) = ballRetraction z r x :=
    fun x => ballRetraction_of_mem z hr (ballRetraction_mem z hr x)
  simpa only [projectedDiscreteHarmonicExtension, interpolatedExitExpectation, hidem] using h

/-- Convergence in probability transfers across a vanishing difference. -/
theorem tendstoInProbability_of_sub_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : ℝ → Ω → ℝ} {h : Ω → ℝ} (hg : TendstoInProbability P g h)
    (hfg : TendstoInProbability P (fun ε ω => f ε ω - g ε ω) (fun _ => 0)) :
    TendstoInProbability P f h := by
  intro δ hδ
  have ha := hg (δ / 2) (by linarith)
  have hb := hfg (δ / 2) (by linarith)
  have hs := ha.add hb
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le) fun ε => ?_
  calc
    P {ω | δ < |f ε ω - h ω|} ≤
        P ({ω | δ / 2 < |g ε ω - h ω|} ∪
          {ω | δ / 2 < |(f ε ω - g ε ω) - 0|}) := by
      apply measure_mono
      intro ω hω
      simp only [mem_ofPred_eq, mem_union] at *
      by_contra hn
      simp only [not_or, not_lt, sub_zero] at hn
      have ht := abs_add_le (g ε ω - h ω) (f ε ω - g ε ω)
      have heq : (g ε ω - h ω) + (f ε ω - g ε ω) = f ε ω - h ω := by ring
      rw [heq] at ht
      linarith
    _ ≤ _ := measure_union_le _ _

/-- The corrected pointwise convergence follows from the continuous-mapping
step and the projected exit-cell comparison. -/
theorem correctedHarmonic_pointwise_of_projectedExit (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) (hcell : CorrectedProjectedExitCellStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (closedBall z r)) (hy : y ∈ ball z r) :
    TendstoInProbability S.P (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y)
      (fun ω => ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
        ∂planarBrownianMotion y) :=
  tendstoInProbability_of_sub_zero
    (continuousBoundary_interpolatedExit_of_inputs 𝒮 h211 hexc hX hγ hγ2 S hS hr hy hψ)
    (hcell γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ y hy)

end MatedCRT

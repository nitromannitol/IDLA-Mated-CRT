import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedExit

/-! # Stability of projected exit expectations under boundary approximation -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Integration against a probability measure is contractive for uniformly
close bounded measurable real functions. -/
theorem abs_integral_sub_le_of_uniform_bound {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f g : α → ℝ} {K L δ : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hK : ∀ x, |f x| ≤ K) (hL : ∀ x, |g x| ≤ L)
    (hδ : ∀ x, |f x - g x| ≤ δ) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ δ := by
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable K
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hK x)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable L
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hL x)
  rw [← integral_sub hfi hgi]
  refine (abs_integral_le_integral_abs).trans ?_
  calc
    (∫ x, |f x - g x| ∂μ) ≤ ∫ _x, δ ∂μ :=
      integral_mono_ae (hfi.sub hgi).abs (integrable_const δ) (Eventually.of_forall hδ)
    _ = δ := by rw [integral_const, probReal_univ, one_smul]

/-- Uniform perturbations of boundary data perturb both projected walk exit
expectations by at most the same amount. -/
theorem projectedExit_expectations_stable {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {r : ℝ} {z y : ℂ} (hr : 0 < r) (ε : ℝ) (ω : Ω)
    {ψ φ : ℂ → ℝ} {K L δ : ℝ}
    (hψ : ∀ x ∈ closedBall z r, |ψ x| ≤ K)
    (hφ : ∀ x ∈ closedBall z r, |φ x| ≤ L)
    (hδ : ∀ x ∈ closedBall z r, |ψ x - φ x| ≤ δ) :
    |projectedDiscreteHarmonicExtension S r z ψ ε ω y -
      projectedDiscreteHarmonicExtension S r z φ ε ω y| ≤ δ ∧
    |interpolatedExitExpectation S r z y ψ ε ω -
      interpolatedExitExpectation S r z y φ ε ω| ≤ δ := by
  constructor
  · apply abs_integral_sub_le_of_uniform_bound
    · exact (measurable_of_countable fun j : ℤ => ψ (ballRetraction z r
        (vertexPoint ε (S.η ω) j))).comp (measurable_vExitPosition _)
    · exact (measurable_of_countable fun j : ℤ => φ (ballRetraction z r
        (vertexPoint ε (S.η ω) j))).comp (measurable_vExitPosition _)
    · exact fun x => hψ _ (ballRetraction_mem z hr _)
    · exact fun x => hφ _ (ballRetraction_mem z hr _)
    · exact fun x => hδ _ (ballRetraction_mem z hr _)
  · apply abs_integral_sub_le_of_uniform_bound
    · exact measurable_exitPosition_interpolatedWalk ε (S.mε ε) (S.η ω)
        (U := ball z r) (φ := fun x => ψ (ballRetraction z r x))
    · exact measurable_exitPosition_interpolatedWalk ε (S.mε ε) (S.η ω)
        (U := ball z r) (φ := fun x => φ (ballRetraction z r x))
    · exact fun x => hψ _ (ballRetraction_mem z hr _)
    · exact fun x => hφ _ (ballRetraction_mem z hr _)
    · exact fun x => hδ _ (ballRetraction_mem z hr _)

/-- Uniform approximation by boundary data whose retractions are Hölder
extends the exit-cell comparison to the approximated data. -/
theorem correctedProjectedExit_of_uniform_approximations (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    {ψ : ℂ → ℝ} {K : ℝ} (hψ : ∀ x ∈ closedBall z r, |ψ x| ≤ K)
    (happrox : ∀ η : ℝ, 0 < η → ∃ (φ : ℂ → ℝ) (L : ℝ),
      (∀ x ∈ closedBall z r, |φ x| ≤ L) ∧
      (∀ x ∈ closedBall z r, |ψ x - φ x| ≤ η) ∧
      ∃ s : ℝ, 0 < s ∧
        IsHolderContinuousOn (fun x => φ (ballRetraction z r x)) (closedBall z (r + s)))
    (hy : y ∈ ball z r) :
    TendstoInProbability S.P
      (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y -
        interpolatedExitExpectation S r z y ψ ε ω) (fun _ => 0) := by
  intro δ hδ
  obtain ⟨φ, L, hφ, hclose, hholder⟩ := happrox (δ / 8) (by linarith)
  have hconv := correctedProjectedExit_of_holder_retraction 𝒮 h211 hmeps hexc hX h28
    hγ hγ2 hρ hρ1 S hS hr hball hholder hy (δ / 2) (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ => zero_le) fun ε => ?_
  apply measure_mono
  intro ω hω
  have hb := projectedExit_expectations_stable S (y := y) hr ε ω hψ hφ hclose
  simp only [mem_ofPred_eq, sub_zero] at hω ⊢
  have ht1 := abs_add_le
    (projectedDiscreteHarmonicExtension S r z ψ ε ω y -
      projectedDiscreteHarmonicExtension S r z φ ε ω y)
    (projectedDiscreteHarmonicExtension S r z φ ε ω y -
      interpolatedExitExpectation S r z y φ ε ω)
  have ht2 := abs_add_le
    ((projectedDiscreteHarmonicExtension S r z ψ ε ω y -
      projectedDiscreteHarmonicExtension S r z φ ε ω y) +
      (projectedDiscreteHarmonicExtension S r z φ ε ω y -
        interpolatedExitExpectation S r z y φ ε ω))
    (interpolatedExitExpectation S r z y φ ε ω -
      interpolatedExitExpectation S r z y ψ ε ω)
  have heq : (projectedDiscreteHarmonicExtension S r z ψ ε ω y -
      projectedDiscreteHarmonicExtension S r z φ ε ω y) +
      (projectedDiscreteHarmonicExtension S r z φ ε ω y -
        interpolatedExitExpectation S r z y φ ε ω) +
      (interpolatedExitExpectation S r z y φ ε ω -
        interpolatedExitExpectation S r z y ψ ε ω) =
      projectedDiscreteHarmonicExtension S r z ψ ε ω y -
        interpolatedExitExpectation S r z y ψ ε ω := by ring
  rw [heq, abs_sub_comm (interpolatedExitExpectation S r z y φ ε ω)] at ht2
  linarith [hb.1, hb.2]

end MatedCRT

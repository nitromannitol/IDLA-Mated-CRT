import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialSampleCoverage
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalShellCutoff

/-! The initial boundary estimate supplies the field cutoff for shell radii.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- The delayed radii of any shell sequence with the prescribed initial shell
stay below a positive field-measurable cutoff on every decreasing prefix. -/
theorem tendsToOneOn_initialShellRadius_le_field_cutoff
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (Θ : ℝ → Ω → ℕ → Set ℤ) (n : ℝ → Ω → ℕ)
    (hinit : ∀ ε ω, Θ ε ω 0 = cellVertices ε (S.η ω) (Λ ω t))
    (K α q : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hq : 0 < q) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω |
      let O : ℕ → ℝ := fun k => ⨆ b : vBoundary (S.mult ε ω) (Θ ε ω k),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b
      ∀ k ≤ n ε ω, (∀ j < k, O (j + 1) ≤ O j) →
        delayedShellRadius O (ε * K) α (ε ^ q) k ≤ dd ω}) := by
  let O : ℝ → Ω → ℕ → ℝ := fun ε ω k =>
    ⨆ b : vBoundary (S.mult ε ω) (Θ ε ω k),
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b
  let G : ℝ → Set Ω := fun ε => {ω | 0 < ε}
  have hG : ProbTendsToOne S.P G := by
    unfold ProbTendsToOne
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hp : 0 < ε := hε
    simp [G, hp]
  have hdata : ∀ ε ω, ω ∈ G ε → 0 ≤ O ε ω 0 ∧ ∀ k < n ε ω, 0 ≤ O ε ω k := by
    intro ε ω hε
    have hp : 0 < ε := hε
    exact ⟨Real.iSup_nonneg fun b => stoppedOdometer_nonneg hp ht b,
      fun k _ => Real.iSup_nonneg fun b => stoppedOdometer_nonneg hp ht b⟩
  have hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn S.P
      {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω | ε * O ε ω 0 ≤ a}) := by
    intro a ha
    have h := initial_boundary_odometer_tendsToZero_of_measurable_exit
      𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht hexit a ha
    have hevents : (fun ε => {ω | ε * O ε ω 0 ≤ a}) =
        (fun ε => {ω | ε * (⨆ b : vBoundary (S.mult ε ω)
          (cellVertices ε (S.η ω) (Λ ω t)),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b) ≤ a}) := by
      funext ε
      ext ω
      dsimp [O]
      rw [hinit]
    rw [hevents]
    exact h
  exact tendsToOneOn_delayedShellRadius_le_field_cutoff S hS
    {ω | t < clusterExitTime (Λ ω) ρ} dd hdd hpos O n K α q hK hα hq G hG hdata hsmall

end MatedCRT.Sec7

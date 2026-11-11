import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialSampleCoverage
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalInitialMaximum

/-! The initial boundary maximum supplies the logarithmic dyadic budget.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Before a null-measurable exit, the floored initial boundary maximum has a
vanishing mesh-normalized logarithmic dyadic budget. -/
theorem initial_boundary_floored_log_budget_tendsToZero
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hmesh : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (K b α c : ℝ) (hK : 0 ≤ K) (hb : b < 1) (hα : 0 < α) (hc : 0 < c) :
    ∀ a : ℝ, 0 < a → TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      (fun ε => {ω |
        let O := ⨆ v : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v
        let x := max O (ε ^ (-b)) * (ε * K)
        x ^ α * (1 + |Real.log ((c / 8) * (x * (1 / 2 : ℝ)) ^ α)| +
          |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2 ≤ a}) := by
  let G : ℝ → Set Ω := fun ε => {ω | 0 < ε}
  have hG : ProbTendsToOne S.P G := by
    unfold ProbTendsToOne
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hp : 0 < ε := hε
    simp [G, hp]
  apply tendsToOneOn_floored_initial_log_budget S.P
    {ω | t < clusterExitTime (Λ ω) ρ}
    (fun ε ω => ⨆ v : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v) hK hb hα hc G hG
  · intro ε ω hω
    exact le_of_lt hω
  · exact initial_boundary_odometer_tendsToZero_of_measurable_exit
      𝒮 h41 h33 hmesh γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht hexit

end MatedCRT.Sec7

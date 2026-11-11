import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialShellCutoff
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ExitMeasurable

/-! Delayed shell cutoff from cone scaling.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Cone scaling supplies the exit measurability needed in the initial shell
cutoff bound. -/
theorem tendsToOneOn_initialShellRadius_le_field_cutoff_of_cone_scaling
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hmesh : MepsScalingInput 𝒮)
    (hcone : ConeEnvironmentScalingStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (Θ : ℝ → Ω → ℕ → Set ℤ) (n : ℝ → Ω → ℕ)
    (hinit : ∀ ε ω, Θ ε ω 0 = cellVertices ε (S.η ω) (Λ ω t))
    (K α q : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hq : 0 < q) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω |
      let O : ℕ → ℝ := fun k => ⨆ b : vBoundary (S.mult ε ω) (Θ ε ω k),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b
      ∀ k ≤ n ε ω, (∀ j < k, O (j + 1) ≤ O j) →
        delayedShellRadius O (ε * K) α (ε ^ q) k ≤ dd ω}) :=
  tendsToOneOn_initialShellRadius_le_field_cutoff 𝒮 h41 h33 hmesh γ hγ hγ' h27 ρ hρ hρ'
    Ω S hS Λ hΛ t ht (nullMeasurableSet_exit_of_cone_scaling hγ hγ' hS h27 hcone Λ hΛ ρ t ht)
    dd hdd hpos Θ n hinit K α q hK hα hq

end MatedCRT.Sec7

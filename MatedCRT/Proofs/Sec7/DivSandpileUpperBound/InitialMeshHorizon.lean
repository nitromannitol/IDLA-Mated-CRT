import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalMeshCertificate
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialSampleCoverage

/-! Initial boundary odometers give a budgeted dyadic shell horizon.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Before a null-measurable cluster exit, the initial boundary odometer
admits a budgeted dyadic horizon with high probability. -/
theorem initial_boundary_budgeted_dyadic_horizon
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hmesh : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (K b α c s T δ q d : ℝ) (hK : 0 < K) (hb : 0 ≤ b) (hb1 : b < 1)
    (hα : 0 < α) (hc : 0 < c) (hs : 0 < s) (hT : 0 ≤ T)
    (hδ : 0 < δ) (hq : 0 < q) (hd : 0 < d) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω |
      let O := ⨆ v : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v
      let S₀ := max O (ε ^ (-b))
      let x := S₀ * (ε * K)
      let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
      let q' := (1 / 2 : ℝ) ^ α
      let r₀ := delayedShellRadius (fun _ => O) (ε * K) α (ε ^ q) 0
      ∃ N n : ℕ,
        S₀ * (1 / 2 : ℝ) ^ N ≤ ε ^ (-b) ∧
        let H := (N : ℝ) * (2 / s + 2) *
          (1 + |Real.log a| + |Real.log q'| * (N : ℝ)) ^ 2
        H < (n : ℝ) ∧ r₀ + (x ^ α * (2 / s + 2) *
          ((1 + |Real.log a| + |Real.log q'|) ^ 2 * T) + ε ^ q * H) +
          (H + 1) * (2 * ε ^ d) ≤ δ}) := by
  let O : ℝ → Ω → ℝ := fun ε ω =>
    ⨆ v : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v
  let G : ℝ → Set Ω := fun ε => {ω | 0 < ε}
  have hG : ProbTendsToOne S.P G := by
    unfold ProbTendsToOne
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hp : 0 < ε := hε
    simp [G, hp]
  apply tendsToOneOn_budgeted_dyadic_horizon_with_mesh_scales S.P
    {ω | t < clusterExitTime (Λ ω) ρ} O hK hb hb1 hα hc hs hT hδ hq hd G hG
  · intro ε ω hε
    exact Real.iSup_nonneg fun v => stoppedOdometer_nonneg hε ht v
  · exact initial_boundary_odometer_tendsToZero_of_measurable_exit
      𝒮 h41 h33 hmesh γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht hexit

end MatedCRT.Sec7

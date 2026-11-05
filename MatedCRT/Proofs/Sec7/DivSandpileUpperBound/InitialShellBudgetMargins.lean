import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialDelayedShells
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialMeshHorizon
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialShellMargins

/-! Simultaneous shell budgets and geometric margins before exit.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- The chosen delayed shells have a budgeted horizon and all geometric
margins simultaneously, with high probability before the cluster exits. -/
theorem initial_delayed_shell_budget_and_margins
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (K b α c s T δ q d ω₀ : ℝ) (hK : 0 < K) (hb : 0 ≤ b) (hb1 : b < 1)
    (hα : 0 < α) (hc : 0 < c) (hc1 : c ≤ 1) (hs : 0 < s) (hT : 0 ≤ T)
    (hδ : 0 < δ) (hq : 0 < q) (hqd : q < d) (hqω : q < ω₀) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω |
      let Θ := initialDelayedShells S Λ ρ t K α q ε ω
      let O : ℕ → ℝ := fun k => ⨆ v : vBoundary (S.mult ε ω) (Θ k),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v
      let r := delayedShellRadius O (ε * K) α (ε ^ q)
      let S₀ := max (O 0) (ε ^ (-b))
      let x := S₀ * (ε * K)
      let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
      let q' := (1 / 2 : ℝ) ^ α
      (∃ N n : ℕ,
        S₀ * (1 / 2 : ℝ) ^ N ≤ ε ^ (-b) ∧
        let H := (N : ℝ) * (2 / s + 2) *
          (1 + |Real.log a| + |Real.log q'| * (N : ℝ)) ^ 2
        H < (n : ℝ) ∧ r 0 + (x ^ α * (2 / s + 2) *
          ((1 + |Real.log a| + |Real.log q'|) ^ 2 * T) + ε ^ q * H) +
          (H + 1) * (2 * ε ^ d) ≤ δ) ∧
      ∀ k, (∀ j < k, O (j + 1) ≤ O j) →
        ε ^ d ≤ r k / 2 ∧ r k + 5 * ρ / 12 ≤ ρ ∧
        5 * ρ / 12 + r k / 4 + ε ^ d < ρ / 2 ∧
        5 * ρ / 12 + (((c / 8) * r k + ε ^ d) + r k / 4) + ε ^ d + r k / 4 ≤ ρ ∧
        10 * ε ^ ω₀ ≤ (c / 8) * r k ∧ (c / 8) * r k ≤ dd ω}) := by
  let Θ : ℝ → Ω → ℕ → Set ℤ := initialDelayedShells S Λ ρ t K α q
  have hinit : ∀ ε ω, Θ ε ω 0 = cellVertices ε (S.η ω) (Λ ω t) :=
    fun ε ω => (initialDelayedShells_spec S Λ ρ t K α q ε ω).1
  have hmargins := tendsToOneOn_initial_shell_margins
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht hexit
    dd hdd hpos Θ hinit K α q d ω₀ c hK.le hα hq hqd hqω hc hc1
  have hbudget := initial_boundary_budgeted_dyadic_horizon
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht hexit
    K b α c s T δ q d hK hb hb1 hα hc hs hT hδ hq (by linarith)
  have hboth := tendsToOneOn_inter S.P {ω | t < clusterExitTime (Λ ω) ρ} _ _ hbudget hmargins
  unfold TendsToOneOn at hboth ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hboth
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono
  rintro ω ⟨hE, hbad⟩
  refine ⟨hE, ?_⟩
  rintro ⟨hbudgetω, hmarginsω⟩
  apply hbad
  have hO : (⨆ v : vBoundary (S.mult ε ω) (Θ ε ω 0),
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v) =
      (⨆ v : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v) := by rw [hinit]
  constructor
  · simpa only [Set.mem_ofPred_eq, Θ, delayedShellRadius_zero, hO] using hbudgetω
  · exact hmarginsω

end MatedCRT.Sec7

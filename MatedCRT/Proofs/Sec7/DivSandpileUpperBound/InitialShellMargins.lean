import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialUniformShellCutoff
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DelayedShellMargins

/-! Geometric shell margins before the continuum exit time.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Polynomial mesh scales and initial-boundary convergence imply all ambient
and survival-test margins for every decreasing shell prefix. -/
theorem tendsToOneOn_initial_shell_margins
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (Θ : ℝ → Ω → ℕ → Set ℤ)
    (hinit : ∀ ε ω, Θ ε ω 0 = cellVertices ε (S.η ω) (Λ ω t))
    (K α q d ω₀ c : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hq : 0 < q)
    (hqd : q < d) (hqω : q < ω₀) (hc : 0 < c) (hc1 : c ≤ 1) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω |
      let O : ℕ → ℝ := fun k => ⨆ b : vBoundary (S.mult ε ω) (Θ ε ω k),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b
      ∀ k, (∀ j < k, O (j + 1) ≤ O j) →
        let r := delayedShellRadius O (ε * K) α (ε ^ q) k
        ε ^ d ≤ r / 2 ∧ r + 5 * ρ / 12 ≤ ρ ∧
        5 * ρ / 12 + r / 4 + ε ^ d < ρ / 2 ∧
        5 * ρ / 12 + (((c / 8) * r + ε ^ d) + r / 4) + ε ^ d + r / 4 ≤ ρ ∧
        10 * ε ^ ω₀ ≤ (c / 8) * r ∧ (c / 8) * r ≤ dd ω}) := by
  let U : Ω → ℝ := fun ω => min 1 (min (dd ω) ((ρ / 2 - 5 * ρ / 12) / 4))
  have hUmeas : Measurable[S.fieldSigma] U := measurable_const.min (hdd.min measurable_const)
  have hU : ∀ ω, 0 < U ω := by
    intro ω
    dsimp [U]
    exact lt_min zero_lt_one (lt_min (hpos ω) (by linarith))
  have hcut := tendsToOneOn_initialShellRadius_le_field_cutoff_all
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht hexit
    U hUmeas hU Θ hinit K α q hK hα hq
  have hfloor : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ε ^ d ≤ ε ^ q / 2 ∧ 10 * ε ^ ω₀ ≤ (c / 8) * ε ^ q := by
    filter_upwards [eventually_mul_rpow_lt_mul_rpow (A := 2) (B := 1) hqd (by norm_num),
      eventually_shell_survival_floor hqω hc] with ε hdiam hsurv
    constructor <;> linarith
  unfold TendsToOneOn at hcut ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcut
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, hfloor] with ε hε hfloor
  apply measure_mono
  rintro ω ⟨hE, hbad⟩
  refine ⟨hE, ?_⟩
  intro hcut
  apply hbad
  dsimp only at hcut ⊢
  let O : ℕ → ℝ := fun k => ⨆ b : vBoundary (S.mult ε ω) (Θ ε ω k),
    stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b
  have hfloorU : ε ^ q ≤ U ω :=
    ((delayedShellRadius_bounds O (ε * K) α (ε ^ q)).2.2 0).trans
      (hcut 0 (by simp))
  have hD0 : 0 ≤ ε ^ d := Real.rpow_nonneg hε.le _
  have hDU : ε ^ d ≤ U ω := by
    have hq0 : 0 ≤ ε ^ q := Real.rpow_nonneg hε.le _
    linarith
  have hgeom := (shell_radius_cutoff_of_half_radius_gap (5 * ρ / 12) ρ c (dd ω)
    (by positivity) (by linarith) hc1 (hpos ω)).2.2.2 (ε ^ d) hD0 hDU
  intro k hprev
  exact delayed_shell_margins_of_envelope O (ε * K) α (ε ^ q) ε ω₀ (U ω) (ε ^ d)
    (5 * ρ / 12) ρ c (dd ω) (k + 1) hc.le
    (fun j _ hp => hcut j hp) hfloor.1 hgeom.1 hgeom.2.1 hgeom.2.2.1 hfloor.2
    hgeom.2.2.2 k (by omega) hprev

end MatedCRT.Sec7

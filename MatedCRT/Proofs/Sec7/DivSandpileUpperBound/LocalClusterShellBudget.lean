import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialShellBudgetMargins
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialBoundaryLocalCover

/-! Shell budget estimates from bounded-cluster localization.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Before cluster exit, the initial boundary odometer
admits a budgeted dyadic horizon with high probability. -/
theorem initial_boundary_budgeted_dyadic_horizon_of_local_cluster_cover
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hmesh : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
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
  · exact initial_boundary_odometer_tendsToZero_of_local_cluster_cover
      𝒮 h41 h33 hmesh γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht


/-- Before exit, every decreasing prefix of a shell sequence initialized by
harmonic-ball cells obeys the field-measurable radius cutoff. -/
theorem tendsToOneOn_initialShellRadius_le_field_cutoff_all_of_local_cluster_cover
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
        (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (Θ : ℝ → Ω → ℕ → Set ℤ)
    (hinit : ∀ ε ω, Θ ε ω 0 = cellVertices ε (S.η ω) (Λ ω t))
    (K α q : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hq : 0 < q) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω |
      let O : ℕ → ℝ := fun k => ⨆ b : vBoundary (S.mult ε ω) (Θ ε ω k),
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b
      ∀ k, (∀ j < k, O (j + 1) ≤ O j) →
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
  have hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn S.P
      {ω | t < clusterExitTime (Λ ω) ρ} (fun ε => {ω | ε * O ε ω 0 ≤ a}) := by
    intro a ha
    have h := initial_boundary_odometer_tendsToZero_of_local_cluster_cover
      𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht a ha
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
  exact tendsToOneOn_delayedShellRadius_le_field_cutoff_all S hS
    {ω | t < clusterExitTime (Λ ω) ρ} dd hdd hpos O K α q hK hα hq G hG
    (fun ε ω hε k => Real.iSup_nonneg fun b => stoppedOdometer_nonneg hε ht b) hsmall


/-- Polynomial mesh scales and initial-boundary convergence imply all ambient
and survival-test margins for every decreasing shell prefix. -/
theorem tendsToOneOn_initial_shell_margins_of_local_cluster_cover
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
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
  have hcut := tendsToOneOn_initialShellRadius_le_field_cutoff_all_of_local_cluster_cover
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht
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


/-- The chosen delayed shells have a budgeted horizon and all geometric
margins simultaneously, with high probability before the cluster exits. -/
theorem initial_delayed_shell_budget_and_margins_of_local_cluster_cover
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (h27 : VolumeGrowthStmt)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t)
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
  have hmargins := tendsToOneOn_initial_shell_margins_of_local_cluster_cover
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht
    dd hdd hpos Θ hinit K α q d ω₀ c hK.le hα hq hqd hqω hc hc1
  have hbudget := initial_boundary_budgeted_dyadic_horizon_of_local_cluster_cover
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht
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

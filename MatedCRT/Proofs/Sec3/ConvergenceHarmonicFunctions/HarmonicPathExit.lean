import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelope
import MatedCRT.Proofs.LBM.AlmostSureRegularExit
import MatedCRT.Proofs.LBM.ExitPosition
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions

/-!
# Lemma 3.6, continuous-mapping step

Theorem 2.11 is extended to the exit-position functional `w ↦ ψ(w(τ_{B_r(z)}))`
(paper, display (eq:rw-to-lbm-harmonic)), which is continuous for the local uniform
distance at every continuous path that leaves `cl(B_r(z))` immediately after its exit
time. Rescaled Liouville Brownian motion has such a regular exit almost surely, by the
Brownian regular-exit input `BrownianOutwardExcursionAtExitStep`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-! ## The radial retraction onto a closed disk -/

theorem continuous_ballRetraction (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Continuous (ballRetraction z r) := by
  unfold ballRetraction
  have hden : Continuous fun x : ℂ => max r (dist x z) :=
    continuous_const.max (continuous_id.dist continuous_const)
  have hq : Continuous fun x : ℂ => r / max r (dist x z) :=
    continuous_const.div hden fun x => (hr.trans_le (le_max_left _ _)).ne'
  exact continuous_const.add ((Complex.continuous_ofReal.comp hq).mul
    (continuous_id.sub continuous_const))

theorem ballRetraction_of_mem (z : ℂ) {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ closedBall z r) : ballRetraction z r x = x := by
  unfold ballRetraction
  rw [max_eq_left (mem_closedBall.mp hx), div_self hr.ne', Complex.ofReal_one, one_mul,
    add_sub_cancel]

theorem ballRetraction_mem (z : ℂ) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    ballRetraction z r x ∈ closedBall z r := by
  rw [mem_closedBall, ballRetraction, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, ← dist_eq_norm]
  have hmax : 0 < max r (dist x z) := hr.trans_le (le_max_left _ _)
  rw [abs_of_nonneg (div_nonneg hr.le hmax.le), div_mul_eq_mul_div, div_le_iff₀ hmax]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr.le

/-! ## Elementary facts on convergence in probability -/

theorem tendstoInProbability_const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ → Ω → ℝ} {Y : Ω → ℝ} (h : TendstoInProbability P X Y) {c : ℝ} (hc : 0 < c) :
    TendstoInProbability P (fun ε ω => c * X ε ω) (fun ω => c * Y ω) := by
  intro δ hδ
  refine (h (δ / c) (div_pos hδ hc)).congr fun ε => ?_
  congr 1
  refine Set.ext fun ω => ?_
  change δ / c < |X ε ω - Y ω| ↔ δ < |c * X ε ω - c * Y ω|
  rw [← mul_sub, abs_mul, abs_of_pos hc, div_lt_iff₀ hc, mul_comm]

theorem TendstoInProbability.congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ → Ω → ℝ} {Y Y' : Ω → ℝ} (h : TendstoInProbability P X Y) (hY : Y =ᵐ[P] Y') :
    TendstoInProbability P X Y' := by
  intro δ hδ
  refine (h δ hδ).congr fun ε => measure_congr (hY.mono fun ω hω => ?_)
  change (δ < |X ε ω - Y ω|) = (δ < |X ε ω - Y' ω|)
  rw [hω]

/-! ## Continuity of the exit-position functional at a regular exit -/

theorem pathFunctionalContinuousAt_exitPosition {φ : ℂ → ℝ} (hφ : Continuous φ) (K : ℝ)
    (p : ContinuousPath ℂ) (z : ℂ) (r : ℝ)
    (hfin : ContinuousPath.exitTime (ball z r) p < ⊤)
    (hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) p).toNNReal,
      p t ∉ closedBall z r) :
    PathFunctionalContinuousAt (fun w => φ (pathExitPosition (ball z r) w) / K) p := by
  have hpos : pathExitPosition (ball z r) p =
      p (ContinuousPath.exitTime (ball z r) p).toNNReal := by
    unfold pathExitPosition
    rw [show pathExitTime (ball z r) ⇑p = ContinuousPath.exitTime (ball z r) p from rfl,
      ContinuousPath.untopD_exitTime]
  intro η hη
  have ht := tendsto_ball_exitPosition_of_localUniformDist
    (l := comap (fun v => localUniformDist v p) (𝓝 0)) p z r hfin hregular (fun v => v)
    tendsto_comap
  have hG : Tendsto (fun v : ℝ≥0 → ℂ => φ (pathExitPosition (ball z r) v) / K)
      (comap (fun v => localUniformDist v p) (𝓝 0))
      (𝓝 (φ (pathExitPosition (ball z r) p) / K)) := by
    rw [hpos]
    exact ((hφ.tendsto _).comp ht).div_const K
  obtain ⟨ρ, hρ, hball⟩ := ((Metric.nhds_basis_ball.comap _).eventually_iff).1
    (Metric.tendsto_nhds.1 hG η hη)
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  have hv' : v ∈ (fun v => localUniformDist v p) ⁻¹' ball 0 ρ := by
    change dist (localUniformDist v p) 0 < ρ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (localUniformDist_nonneg v p)]
    exact hv
  have := hball hv'
  rw [Real.dist_eq] at this
  exact this.le

/-! ## The step -/

/-- The normalized exit-value functional `w ↦ ψ(R(w(τ_{B_r(z)}))) / K`, `R` the
retraction onto `cl(B_r(z))`. -/
noncomputable def exitValueFunctional (z : ℂ) (r : ℝ) (ψ : ℂ → ℝ) (K : ℝ)
    (w : ℝ≥0 → ℂ) : ℝ :=
  ψ (ballRetraction z r (pathExitPosition (ball z r) w)) / K

theorem abs_exitValueFunctional_le_one {z : ℂ} {r : ℝ} {ψ : ℂ → ℝ} {K : ℝ} (hK : 0 < K)
    (hψ : ∀ x, |ψ (ballRetraction z r x)| ≤ K) (w : ℝ≥0 → ℂ) :
    |exitValueFunctional z r ψ K w| ≤ 1 := by
  rw [exitValueFunctional, abs_div, abs_of_pos hK, div_le_one hK]
  exact hψ _

theorem MatedCRTEnv.IsValid.m₀_pos {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) :
    0 < S.m₀ := by
  have hc := matedCRTScalingConstantPositive 𝒮 γ hγ hγ2 Ω S hS
  have hdiv : 0 < (2 : ℝ) / S.m₀ := by
    simp only [MatedCRTEnv.c₀] at hc
    linarith
  exact (div_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp hdiv

/-- Almost surely, the exit-value functional is continuous at the rescaled LBM path. -/
theorem MatedCRTEnv.IsValid.ae_continuousAt_exitValueFunctional {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    (hexc : BrownianOutwardExcursionAtExitStep) {y z : ℂ} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ ball z r) {ψ : ℂ → ℝ} (hψR : Continuous fun x => ψ (ballRetraction z r x))
    (K : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, PathFunctionalContinuousAt
      (exitValueFunctional z r ψ K) (rescaledLBMPath (S.clock ω) S.m₀ b) := by
  have hreg := hS.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion
    (hS.m₀_pos hγ hγ2) hy (hexc y z r hy)
  filter_upwards [hS.isLQGClock, hreg,
    hS.ae_normalizedLBMExitTime_any_ball_lt_top hγ hγ2 y z r] with ω hcω hregω hfinω
  filter_upwards [(hcω y).2, hregω, hfinω] with b hclock hregb hfinb
  have hregb' : ∃ᶠ t in 𝓝[>] (pathExitTime (ball z r)
      (rescaledLBMPath (S.clock ω) S.m₀ b)).toNNReal,
      rescaledLBMPath (S.clock ω) S.m₀ b t ∉ closedBall z r := by
    rw [← closure_ball z hr.ne']
    exact hregb
  exact pathFunctionalContinuousAt_exitPosition hψR K
    ⟨rescaledLBMPath (S.clock ω) S.m₀ b, continuous_rescaledLBMPath hclock⟩ z r hfinb hregb'

/-- Convergence in probability of the expected normalized exit value. -/
theorem tendstoInProbability_exitValueFunctional (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) (hW : InterpolatedWalkMeasurableStep)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) {y z : ℂ} {r : ℝ} (hr : 0 < r) (hy : y ∈ ball z r) {ψ : ℂ → ℝ}
    (hψR : Continuous fun x => ψ (ballRetraction z r x)) {K : ℝ} (hK : 0 < K)
    (hψK : ∀ x, |ψ (ballRetraction z r x)| ≤ K) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, exitValueFunctional z r ψ K (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂(srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)))
      (fun ω => ∫ b, exitValueFunctional z r ψ K (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂(planarBrownianMotion y)) := by
  have := hS.isProbabilityMeasure
  exact tendstoInProbability_of_ae_continuous_pathFunctional S.P
    (fun ε ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) (fun _ _ => inferInstance)
    (fun ε ω => interpolatedWalk ε (S.η ω) (S.mε ε))
    (fun _ => planarBrownianMotion y) (fun _ => inferInstance)
    (fun ω => rescaledLBMPath (S.clock ω) S.m₀)
    (fun F hF => h211 γ hγ hγ2 Ω S hS {y} isCompact_singleton y (mem_singleton y) F hF)
    (exitValueFunctional z r ψ K) (abs_exitValueFunctional_le_one hK hψK)
    (fun ε ω => by
      have h := (hW ε (S.mε ε) (S.η ω) (S.mult ε ω) (vertexOf ε (S.η ω) y)).2 (ball z r)
        isOpen_ball (fun x => ψ (ballRetraction z r x) / K) (hψR.div_const K)
      exact h)
    (fun F hF ε ω => (hW ε (S.mε ε) (S.η ω) (S.mult ε ω) (vertexOf ε (S.η ω) y)).1 F hF)
    (fun F hF => (hX γ hγ hγ2 Ω S hS y F hF).1)
    (fun F hF => (hX γ hγ hγ2 Ω S hS y F hF).2)
    (hS.ae_continuousAt_exitValueFunctional hγ hγ2 hexc hr hy hψR K)

/-- **The continuous-mapping step of Lemma 3.6.** -/
theorem harmonicPathExitStep_of_steps (𝒮 : SpaceFillingSLEModel)
    (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) (hW : InterpolatedWalkMeasurableStep) :
    HarmonicPathExitStep 𝒮 := by
  intro h211 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ y hy
  obtain ⟨s, hs, C₀, χ, hχ, -, hhol⟩ := hψ
  have hcont : ContinuousOn ψ (closedBall z r) :=
    (hhol.continuousOn hχ).mono (closedBall_subset_closedBall (by linarith))
  have hψR : Continuous fun x => ψ (ballRetraction z r x) :=
    hcont.comp_continuous (continuous_ballRetraction z hr) (ballRetraction_mem z hr)
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hcont
  have hKpos : 0 < |C| + 1 := by positivity
  have hψK : ∀ x, |ψ (ballRetraction z r x)| ≤ |C| + 1 := fun x => by
    have h1 := hC _ (ballRetraction_mem z hr x)
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self C]
  have hK := tendstoInProbability_const_mul
    (tendstoInProbability_exitValueFunctional 𝒮 h211 hexc hX hW hγ hγ2 S hS hr hy hψR hKpos
      hψK) hKpos
  have hL : ∀ ε ω, (|C| + 1) * ∫ x, exitValueFunctional z r ψ (|C| + 1)
      (interpolatedWalk ε (S.η ω) (S.mε ε) x) ∂(srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) =
      interpolatedExitExpectation S r z y ψ ε ω := fun ε ω => by
    rw [interpolatedExitExpectation, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change (|C| + 1) * (ψ (ballRetraction z r (pathExitPosition (ball z r)
      (interpolatedWalk ε (S.η ω) (S.mε ε) x))) / (|C| + 1)) = _
    field_simp
  simp only [hL] at hK
  refine hK.congr_ae ?_
  filter_upwards [hS.ae_normalizedLBMExitPosition_mem_sphere hγ hγ2 hy] with ω hω
  rw [← integral_const_mul]
  refine integral_congr_ae (hω.mono fun b hb => ?_)
  change (|C| + 1) * (ψ (ballRetraction z r (pathExitPosition (ball z r)
    (rescaledLBMPath (S.clock ω) S.m₀ b))) / (|C| + 1)) = _
  rw [ballRetraction_of_mem z hr (sphere_subset_closedBall hb)]
  field_simp

end MatedCRT

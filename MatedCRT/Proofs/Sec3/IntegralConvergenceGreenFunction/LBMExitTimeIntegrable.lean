import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrableBound
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Final

/-!
# Lemma 3.4 input: integrability of the LBM exit time

`lbmExitTimeIntegrableStep_of_inputs` proves `LBMExitTimeIntegrableStep 𝒮` from the named inputs of the
Section 3 assembly: the bounded exit-time and exit-time-tail statements, `MepsScalingInput`, the walk convergence
`RandomWalkToLBMStmt` (Theorem 2.11), the cell-size estimate `CellSizeEstimateStmt`, the measurability
`LBMPathFunctionalMeasurableStep` and the Brownian excursion `BrownianOutwardExcursionAtExitStep`.

The proof: for each inner ball `B(z, s_j)`, `s_j ↑ r`, the truncations `min(τ_j, j)` of the LBM exit time are
bounded in expectation by the same random constant (`ae_lbm_integral_le_inner`); they increase to the exit time
of `B(z, r)` along continuous paths; monotone convergence gives a finite lower integral, hence integrability.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The truncations `min(τ_D(w), j)` are monotone in `j` for an increasing sequence of balls. -/
theorem min_pathExitTime_monotone {z : ℂ} (s : ℕ → ℝ) (hs_mono : Monotone s) (w : ℝ≥0 → ℂ) :
    Monotone fun j : ℕ => min (pathExitTime (ball z (s j)) w) (j : ℝ≥0∞) := by
  refine monotone_nat_of_le_succ fun j => min_le_min ?_ ?_
  · exact pathExitTime_mono_set (ball_subset_ball (hs_mono (Nat.le_succ j))) w
  · exact_mod_cast Nat.le_succ j

/-- For continuous paths, the truncated inner exit times increase to the exit time of the outer ball. -/
theorem iSup_min_pathExitTime_eq {z : ℂ} {r : ℝ} (s : ℕ → ℝ) (hs_mono : Monotone s)
    (hs_lt : ∀ k, s k < r) (hs_lim : Tendsto s atTop (𝓝 r)) {w : ℝ≥0 → ℂ} (hw : Continuous w) :
    ⨆ j : ℕ, min (pathExitTime (ball z (s j)) w) (j : ℝ≥0∞) = pathExitTime (ball z r) w := by
  apply le_antisymm
  · refine iSup_le fun j => (min_le_left _ _).trans ?_
    exact pathExitTime_mono_set (ball_subset_ball (hs_lt j).le) w
  · rw [← pathExitTime_iSup_ball s hs_lt hs_lim hw]
    refine iSup_le fun j => ?_
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨m₁, hm₁⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    have hjm : j ≤ m₁ + j := Nat.le_add_left j m₁
    have hmm : (m₁ : ℝ≥0∞) ≤ ((m₁ + j : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_add_right m₁ j
    calc c < min (pathExitTime (ball z (s j)) w) ((m₁ + j : ℕ) : ℝ≥0∞) :=
          lt_min hc (lt_of_lt_of_le hm₁ hmm)
      _ ≤ min (pathExitTime (ball z (s (m₁ + j))) w) ((m₁ + j : ℕ) : ℝ≥0∞) :=
          min_le_min (pathExitTime_mono_set (ball_subset_ball (hs_mono hjm)) w) le_rfl
      _ ≤ ⨆ m : ℕ, min (pathExitTime (ball z (s m)) w) (m : ℝ≥0∞) :=
          le_iSup (fun m : ℕ => min (pathExitTime (ball z (s m)) w) (m : ℝ≥0∞)) (m₁ + j)

/-- **Monotone limit of truncations.** If the truncations are monotone, have the sup `τ_D` a.e., and their lower
integrals are bounded by `K`, then `τ_D` is a.e. measurable with lower integral at most `K`. -/
theorem aemeasurable_lintegral_le_of_iSup_min {β : Type*} [MeasurableSpace β] {μ : Measure β}
    {τ : ℕ → β → ℝ≥0∞} {τD : β → ℝ≥0∞} {K : ℝ≥0∞}
    (hmeas : ∀ j : ℕ, AEMeasurable (fun b => min (τ j b) (j : ℝ≥0∞)) μ)
    (hmono : ∀ᵐ b ∂μ, Monotone fun j : ℕ => min (τ j b) (j : ℝ≥0∞))
    (hsup : ∀ᵐ b ∂μ, ⨆ j : ℕ, min (τ j b) (j : ℝ≥0∞) = τD b)
    (hbd : ∀ j : ℕ, ∫⁻ b, min (τ j b) (j : ℝ≥0∞) ∂μ ≤ K) :
    AEMeasurable τD μ ∧ ∫⁻ b, τD b ∂μ ≤ K := by
  have hlim : ∀ᵐ b ∂μ, Tendsto (fun j : ℕ => min (τ j b) (j : ℝ≥0∞)) atTop (𝓝 (τD b)) := by
    filter_upwards [hmono, hsup] with b hm hs
    rw [← hs]
    exact tendsto_atTop_iSup hm
  refine ⟨aemeasurable_of_tendsto_metrizable_ae atTop hmeas hlim, ?_⟩
  calc ∫⁻ b, τD b ∂μ = ∫⁻ b, ⨆ j : ℕ, min (τ j b) (j : ℝ≥0∞) ∂μ :=
        lintegral_congr_ae (hsup.mono fun b hb => hb.symm)
    _ = ⨆ j : ℕ, ∫⁻ b, min (τ j b) (j : ℝ≥0∞) ∂μ := lintegral_iSup' hmeas hmono
    _ ≤ K := iSup_le hbd

/-- A real bounded nonnegative function whose integral is at most `K.toReal` has lower integral at most `K`. -/
theorem lintegral_ofReal_le_of_integral_le {β : Type*} [MeasurableSpace β] {μ : Measure β}
    [IsProbabilityMeasure μ] {G : β → ℝ} {n : ℕ} {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hGm : AEStronglyMeasurable G μ) (hnn : ∀ b, 0 ≤ G b) (hbd : ∀ b, G b ≤ n)
    (hint : ∫ b, G b ∂μ ≤ K.toReal) :
    ∫⁻ b, ENNReal.ofReal (G b) ∂μ ≤ K := by
  have hI : Integrable G μ :=
    (integrable_const (n : ℝ)).mono' hGm
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn b)]
        exact hbd b)
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hnn)]
  exact (ENNReal.ofReal_le_ofReal hint).trans (ENNReal.ofReal_toReal hK).le

/-- **Integrability of the LBM exit time** from a ball, for almost every environment: the hypothesis of
`integralConvergenceGreenFunction_of_steps`, proved from the named inputs of the Section 3 assembly. -/
theorem lbmExitTimeIntegrableStep_of_inputs {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep) :
    LBMExitTimeIntegrableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy
  have hm0 : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  obtain ⟨α, hα, hmom⟩ := scaled_secondMoment_finite_bound_polyHighProb h17 h18 hscale hγ hγ2
  obtain ⟨B, hB, hmomS⟩ := hmom ρ hρ hρ1
  have hmomE : _root_.HarmonicBalls.PolyHighProb S.P (lbmMomEv S ρ α B) := hmomS Ω S hS
  -- the inner radii `s k = r - ρ₀ / (k + 2)` increase to `r`
  have hd_lt : dist y z < r := mem_ball.1 hy
  have hd0 : 0 ≤ dist y z := dist_nonneg
  set ρ₀ : ℝ := (r - dist y z) / 2 with hρ₀_def
  have hρ₀ : 0 < ρ₀ := by rw [hρ₀_def]; linarith
  set s : ℕ → ℝ := fun k => r - ρ₀ / ((k : ℝ) + 2) with hs_def
  have hdiv_pos : ∀ k : ℕ, 0 < ρ₀ / ((k : ℝ) + 2) := fun k => div_pos hρ₀ (by positivity)
  have hdiv_le : ∀ k : ℕ, ρ₀ / ((k : ℝ) + 2) ≤ ρ₀ := fun k =>
    div_le_self hρ₀.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hs_lt : ∀ k, s k < r := fun k => by
    have := hdiv_pos k
    simp only [hs_def]
    linarith
  have hs_pos : ∀ k, 0 < s k := fun k => by
    have := hdiv_le k
    simp only [hs_def]
    linarith
  have hys : ∀ k, y ∈ ball z (s k) := fun k => by
    rw [mem_ball]
    have := hdiv_le k
    simp only [hs_def]
    linarith
  have hs_mono : Monotone s := by
    refine monotone_nat_of_le_succ fun k => ?_
    have h1 : ρ₀ / (((k + 1 : ℕ) : ℝ) + 2) ≤ ρ₀ / ((k : ℝ) + 2) :=
      div_le_div_of_nonneg_left hρ₀.le (by positivity) (by push_cast; linarith)
    simp only [hs_def]
    linarith
  have hs_lim : Tendsto s atTop (𝓝 r) := by
    have h0 : Tendsto (fun k : ℕ => ρ₀ / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
    have h1 := (tendsto_const_nhds (x := r)).sub h0
    simpa [hs_def] using h1
  -- almost sure facts
  have hbdAll : ∀ᵐ ω ∂S.P, ∀ k n : ℕ,
      ∫ b, truncatedExitFunctional (ball z (s k)) n (rescaledLBMPath (S.clock ω) S.m₀ b)
          ∂planarBrownianMotion y ≤
        (1 + ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2).toReal := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro n
    exact ae_lbm_integral_le_inner hscale h211 hX hcell hexc hγ hγ2 hρ hρ1 hα S hS hr (hs_pos k)
      (hs_lt k) hball (hys k) n hmomE
  have hLfin : ∀ᵐ ω ∂S.P, largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤ := by
    have hT := tendsto_measure_compl_of_polyHighProb hmomE
    have hz : S.P {ω | ¬ largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤} = 0 := by
      refine le_antisymm (ge_of_tendsto hT (Eventually.of_forall fun ε => measure_mono ?_)) zero_le
      intro ω hω hM
      exact hω hM.1
    exact ae_iff.2 hz
  have hfacts : ∀ᵐ ω ∂S.P, ∀ k n : ℕ, ∀ᵐ b ∂planarBrownianMotion y,
      rescaledLBMPath (S.clock ω) S.m₀ b ∈ {w : ℝ≥0 → ℂ | Continuous w} ∧
      PathFunctionalContinuousWithinAt {w : ℝ≥0 → ℂ | Continuous w}
        (truncatedExitFunctional (ball z (s k)) n) (rescaledLBMPath (S.clock ω) S.m₀ b) := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro n
    exact ae_lbm_facts S hS hm0 hexc (hys k) (hs_pos k) n
  have hmeasA : ∀ᵐ ω ∂S.P, ∀ k n j : ℕ,
      AEStronglyMeasurable (fun b => pathUpperEnvelopeOn {w : ℝ≥0 → ℂ | Continuous w}
        (fun v => truncatedExitFunctional (ball z (s k)) n v / ((n : ℝ) + 1)) (j : ℝ)
        (rescaledLBMPath (S.clock ω) S.m₀ b)) (planarBrownianMotion y) := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro j
    have hG' : ∀ w : ℝ≥0 → ℂ, w ∈ {w : ℝ≥0 → ℂ | Continuous w} →
        |truncatedExitFunctional (ball z (s k)) n w / ((n : ℝ) + 1)| ≤ 1 := by
      intro w _
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), div_le_one (by positivity)]
      exact (abs_truncatedExitFunctional_le _ _ _).trans (by linarith)
    have hBL := isBoundedLipschitzPathFunctional_pathUpperEnvelopeOn hG'
      (Nat.cast_nonneg (α := ℝ) j) ⟨fun _ => 0, continuous_const⟩
    exact (hX γ hγ hγ2 Ω S hS y _ hBL).1
  filter_upwards [hbdAll, hLfin, hfacts, hmeasA] with ω hbdω hLω hfacω hmeasω
  have hKtop : (1 + ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hLω.ne)⟩
  -- measurability of the truncated inner functionals in the Brownian variable
  have hGm : ∀ k n : ℕ, AEStronglyMeasurable
      (fun b => truncatedExitFunctional (ball z (s k)) n (rescaledLBMPath (S.clock ω) S.m₀ b))
      (planarBrownianMotion y) := by
    intro k n
    refine aestronglyMeasurable_of_envelopes_scaled (X := fun b => rescaledLBMPath (S.clock ω) S.m₀ b)
      (c := (n : ℝ) + 1) (by positivity) (fun w _ => ?_) (fun j => hmeasω k n j)
      ((hfacω k n).mono fun b hb => ⟨hb.1, hb.2⟩)
    exact (abs_truncatedExitFunctional_le _ _ _).trans (by linarith)
  -- the truncated inner exit times of the outer ball
  have hτmeas : ∀ j : ℕ, AEMeasurable
      (fun b => min (pathExitTime (ball z (s j)) (rescaledLBMPath (S.clock ω) S.m₀ b)) (j : ℝ≥0∞))
      (planarBrownianMotion y) := by
    intro j
    have hfun : (fun b => min (pathExitTime (ball z (s j)) (rescaledLBMPath (S.clock ω) S.m₀ b))
        (j : ℝ≥0∞)) = fun b => ENNReal.ofReal
          (truncatedExitFunctional (ball z (s j)) j (rescaledLBMPath (S.clock ω) S.m₀ b)) := by
      funext b
      rw [ofReal_truncatedExitFunctional]
    rw [hfun]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hGm j j).aemeasurable
  have hbd : ∀ j : ℕ, ∫⁻ b, min (pathExitTime (ball z (s j)) (rescaledLBMPath (S.clock ω) S.m₀ b))
      (j : ℝ≥0∞) ∂planarBrownianMotion y ≤
      (1 + ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2) := by
    intro j
    have hfun : (fun b => min (pathExitTime (ball z (s j)) (rescaledLBMPath (S.clock ω) S.m₀ b))
        (j : ℝ≥0∞)) = fun b => ENNReal.ofReal
          (truncatedExitFunctional (ball z (s j)) j (rescaledLBMPath (S.clock ω) S.m₀ b)) := by
      funext b
      rw [ofReal_truncatedExitFunctional]
    rw [hfun]
    exact lintegral_ofReal_le_of_integral_le hKtop (hGm j j)
      (fun b => truncatedExitFunctional_nonneg _ _ _) (fun b => truncatedExitFunctional_le _ _ _)
      (hbdω j j)
  have hcontω : ∀ᵐ b ∂planarBrownianMotion y,
      Continuous (rescaledLBMPath (S.clock ω) S.m₀ b) := (hfacω 0 0).mono fun b hb => hb.1
  have hmono : ∀ᵐ b ∂planarBrownianMotion y,
      Monotone fun j : ℕ => min (pathExitTime (ball z (s j))
        (rescaledLBMPath (S.clock ω) S.m₀ b)) (j : ℝ≥0∞) :=
    Eventually.of_forall fun b => min_pathExitTime_monotone s hs_mono _
  have hsup : ∀ᵐ b ∂planarBrownianMotion y,
      ⨆ j : ℕ, min (pathExitTime (ball z (s j)) (rescaledLBMPath (S.clock ω) S.m₀ b)) (j : ℝ≥0∞) =
        pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) :=
    hcontω.mono fun b hb => iSup_min_pathExitTime_eq s hs_mono hs_lt hs_lim hb
  obtain ⟨hae, hle⟩ := aemeasurable_lintegral_le_of_iSup_min hτmeas hmono hsup hbd
  exact integrable_toReal_of_lintegral_ne_top hae (ne_top_of_le_ne_top hKtop hle)

end MatedCRT

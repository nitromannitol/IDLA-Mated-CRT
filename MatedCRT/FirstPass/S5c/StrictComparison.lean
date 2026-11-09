import MatedCRT.FirstPass.S5c.StoppedGeometry
import MatedCRT.FirstPass.S5c.PositiveTest
import MatedCRT.FirstPass.S1c.TestLocal
import MatedCRT.FirstPass.Frozen.S5c

/-!
# FIRST PASS, Lemma 5.3 (three-inputs section 3, A7): strict comparison of the least supersolutions on the cluster

For `0 < s < t < T = clusterExitTime Λ ρ`, the margin `A = w_t - (t/s) w_s` (with `w_u = leastSupersolution μ ρ 0 u`)
satisfies `A ≥ 0` on `B̄_ρ` (MassComparison/StoppedGeometry, (3.4)), and on the open connected set `Λ_s`:
`ΔA = (1 - t/s) μ` in the sense of distributions (HasLaplacian of `w_t` on `μ|Λ_t` and of `w_s` on `μ|Λ_s`, with
`Λ_s ⊆ Λ_t`). Hence `ΔA ≤ 0` on `Λ_s`, and the strong minimum principle (external, `FPStrongMinimumPrinciple`, frozen in
Frozen/S5c.lean) gives `A > 0` on `Λ_s`: otherwise `A ≡ 0` on `Λ_s`, so `(1 - t/s) ∫φ dμ = 0` for a test function
`φ ≥ 0` in `Λ_s` with `∫φ dμ > 0` (PositiveTest), contradicting `t > s`. Armitage-Gardiner for the minimum principle;
Duplantier-Sheffield / Berestycki-Powell terminology for the cluster `Λ_s` (the harmonic ball of mass `s`).
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric Laplacian

/-- The margin `w_t - (t/s) w_s` (three-inputs A7), with `w_u = leastSupersolution μ ρ 0 u` (Armitage-Gardiner, least
superharmonic majorant of the obstacle `-u G`). -/
noncomputable def clusterMargin (μ : Measure ℂ) (ρ t s : ℝ) (x : ℂ) : ℝ :=
  leastSupersolution μ ρ 0 t x - (t / s) * leastSupersolution μ ρ 0 s x

/-- A test function supported in `U` is a test function supported in any `V ⊇ U`. -/
theorem isTestFunction_mono {U V : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (hUV : U ⊆ V) :
    IsTestFunction V φ :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩

/-- For a test function `φ` in `U` and `v` continuous on `B̄_ρ ⊇ U`, the integrand `v Δφ` is integrable. -/
theorem integrable_mul_laplacian_of_continuousOn {v : ℂ → ℝ} {ρ : ℝ} {U : Set ℂ} {φ : ℂ → ℝ}
    (hv : ContinuousOn v (closedBall 0 ρ)) (hUρ : U ⊆ closedBall 0 ρ) (hφ : IsTestFunction U φ) :
    Integrable (fun x => v x * Δ φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.2.1
  have hKρ : tsupport φ ⊆ closedBall 0 ρ := hφ.2.2.trans hUρ
  have hLc : Continuous (Δ φ) := continuous_laplacian_of_contDiff (hφ.1.of_le (by norm_num))
  have hΔK : ∀ x, x ∉ tsupport φ → Δ φ x = 0 := fun x hx =>
    laplacian_eq_zero_of_not_mem_tsupport subset_rfl hx
  have hcont : ContinuousOn (fun x => v x * Δ φ x) (tsupport φ) :=
    (hv.mono hKρ).mul hLc.continuousOn
  have hI : IntegrableOn (fun x => v x * Δ φ x) (tsupport φ) :=
    ContinuousOn.integrableOn_compact hK hcont
  have hsupp : Function.support (fun x => v x * Δ φ x) ⊆ tsupport φ := by
    intro x hx
    by_contra h
    apply hx
    simp only [hΔK x h, mul_zero]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hI

/-- Nonnegativity of the margin on `Λ_s` (from (3.4) on the stopped event). -/
theorem clusterMargin_nonneg {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (hfam : IsConeHarmonicBallFamily μ Λ)
    {ρ t s : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ) (hs : 0 < s) (hst : s < t) :
    ∀ x ∈ Λ s, 0 ≤ clusterMargin μ ρ t s x := by
  intro x hx
  have hUρ : Λ s ⊆ closedBall (0 : ℂ) ρ :=
    (subset_ball_of_le_clusterExitTime hfam hT hs hst.le).trans
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have h := leastSupersolution_div_le_of_le_clusterExitTime hfam hρ hT hs hst.le le_rfl x (hUρ hx)
  have ht : 0 < t := lt_trans hs hst
  unfold clusterMargin
  have h2 := mul_le_mul_of_nonneg_left h ht.le
  have e1 : t * (leastSupersolution μ ρ 0 s x / s) = (t / s) * leastSupersolution μ ρ 0 s x := by ring
  have e2 : t * (leastSupersolution μ ρ 0 t x / t) = leastSupersolution μ ρ 0 t x := by
    field_simp
  linarith

/-- **Lemma 5.3, A7 (three-inputs section 3).** For `0 < s < t < T = clusterExitTime Λ ρ`, the margin
`w_t - (t/s) w_s` is strictly positive at every point of the harmonic ball `Λ_s`. Uses the external strong minimum
principle `FPStrongMinimumPrinciple` as an explicit hypothesis. -/
theorem clusterMargin_pos_on_cluster (hmin : FPStrongMinimumPrinciple) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t s : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ)
    (hs : 0 < s) (hst : s < t) :
    ∀ x ∈ Λ s, 0 < clusterMargin μ ρ t s x := by
  have ht : 0 < t := lt_trans hs hst
  have hU : IsOpen (Λ s) := (hfam.1 s hs).1
  have hconn : IsConnected (Λ s) := hfam.2.1.isConnected s hs
  have hUρ : Λ s ⊆ closedBall (0 : ℂ) ρ :=
    (subset_ball_of_le_clusterExitTime hfam hT hs hst.le).trans
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hUball : Λ s ⊆ ball (0 : ℂ) ρ :=
    (subset_ball_of_le_clusterExitTime hfam hT hs hst.le).trans (ball_subset_ball (by linarith))
  have hΛmono : Λ s ⊆ Λ t := hfam.2.1.monotoneOn hs ht hst.le
  have hcont_t : ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall 0 ρ) :=
    continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT ht le_rfl
  have hcont_s : ContinuousOn (leastSupersolution μ ρ 0 s) (closedBall 0 ρ) :=
    continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT hs hst.le
  have hA_cont : ContinuousOn (clusterMargin μ ρ t s) (Λ s) := by
    unfold clusterMargin
    exact ((hcont_t.mono hUρ).sub (continuousOn_const.mul (hcont_s.mono hUρ)))
  have hnonneg := clusterMargin_nonneg hfam hρ hT hs hst
  -- distributional Laplacians of the two least supersolutions (Theorem 2.3(c) at radius ρ)
  have hLapT : HasLaplacian (leastSupersolution μ ρ 0 t) (μ.restrict (Λ t)) 0 (ball 0 ρ) :=
    (hfam.2.2 t (ρ / 3) ht (by linarith) (subset_ball_of_le_clusterExitTime hfam hT ht le_rfl) ρ
      (by linarith)).2.2.1
  have hLapS : HasLaplacian (leastSupersolution μ ρ 0 s) (μ.restrict (Λ s)) 0 (ball 0 ρ) :=
    (hfam.2.2 s (ρ / 3) hs (by linarith) (subset_ball_of_le_clusterExitTime hfam hT hs hst.le) ρ
      (by linarith)).2.2.1
  -- the distributional identity Δ(margin) = (1 - t/s) μ on Λ_s
  have hLap : ∀ φ : ℂ → ℝ, IsTestFunction (Λ s) φ →
      ∫ x, clusterMargin μ ρ t s x * Δ φ x = (1 - t / s) * ∫ x, φ x ∂μ := by
    intro φ hφ
    have hφρ : IsTestFunction (ball 0 ρ) φ := isTestFunction_mono hφ hUball
    have hv := hLapT.2 φ hφρ
    have hw := hLapS.2 φ hφρ
    have ev : ∫ x in Λ t, φ x ∂μ = ∫ x, φ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (hΛmono (hφ.2.2 h)))
    have ew : ∫ x in Λ s, φ x ∂μ = ∫ x, φ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
    have hint_v := integrable_mul_laplacian_of_continuousOn hcont_t
      (hUρ.trans le_rfl) hφ
    have hint_w := integrable_mul_laplacian_of_continuousOn hcont_s hUρ hφ
    have hfun : (fun x => clusterMargin μ ρ t s x * Δ φ x) =
        fun x => leastSupersolution μ ρ 0 t x * Δ φ x
          - (t / s) * (leastSupersolution μ ρ 0 s x * Δ φ x) := by
      funext x
      unfold clusterMargin
      ring
    rw [hfun, integral_sub hint_v (hint_w.const_mul (t / s)), integral_const_mul, hv.2.2, hw.2.2]
    simp only [integral_zero_measure, ev, ew]
    ring
  intro x hx
  by_contra hneg
  have hx0 : clusterMargin μ ρ t s x = 0 := le_antisymm (not_lt.1 hneg) (hnonneg x hx)
  have hLapA : HarmonicBalls.LaplacianLE (clusterMargin μ ρ t s) 0 (Λ s) := by
    refine ⟨hA_cont.locallyIntegrableOn hU.measurableSet, fun φ hφ hφ0 _ => ?_⟩
    rw [hLap φ hφ, integral_zero_measure]
    have hI : 0 ≤ ∫ y, φ y ∂μ := integral_nonneg hφ0
    have hc : 1 ≤ t / s := (one_le_div hs).2 hst.le
    nlinarith [mul_nonneg (sub_nonneg.2 hc) hI]
  have hzero : ∀ y ∈ Λ s, clusterMargin μ ρ t s y = 0 :=
    hmin (Λ s) (clusterMargin μ ρ t s) hU hconn hA_cont hLapA hnonneg x hx hx0
  have hmass : μ (Λ s) = ENNReal.ofReal s := hfam.2.1.measure_eq s hs
  obtain ⟨φ, hφ, _, _, hφpos⟩ := exists_test_integral_pos hU
    (by rw [hmass]; exact ENNReal.ofReal_ne_top) (by rw [hmass]; exact ENNReal.ofReal_pos.2 hs)
  have hzero_int : ∫ y, clusterMargin μ ρ t s y * Δ φ y = 0 := by
    have hfz : (fun y => clusterMargin μ ρ t s y * Δ φ y) = fun _ => 0 := by
      funext y
      by_cases hy : y ∈ Λ s
      · simp [hzero y hy]
      · simp [laplacian_eq_zero_of_not_mem_tsupport hφ.2.2 hy]
    rw [hfz, integral_zero]
  have hneg' : (1 - t / s) < 0 := by
    have : 1 < t / s := (one_lt_div hs).2 hst
    linarith
  have hid := hLap φ hφ
  rw [hzero_int] at hid
  have hp := mul_neg_of_neg_of_pos hneg' hφpos
  linarith

end MatedCRT.S5c

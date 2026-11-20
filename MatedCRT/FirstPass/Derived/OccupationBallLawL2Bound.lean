import MatedCRT.FirstPass.Derived.OccupationBallLawInMeasure

/-!
# Uniform second moment of the occupation integrals under the path law averaged over a disc

If the dyadic approximants of the `γ`-LQG measure give every unit ball centred in `B̄(0, n + 1)` mass
at most `C r^β` (uniformly in the level), then for a measurable `0 ≤ f ≤ K` vanishing off `B̄(0, n)`
the occupation integrals `X_k = ∫_{(0,1]} f ρ_k (b_s) ds` of the approximating clocks have
`ballLaw R`-second moments bounded uniformly in `k`.
-/

open MeasureTheory MarkovProcess Set Filter Topology Metric
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The mass of the weighted approximant densities is bounded uniformly in the level**: covering
`B̄(0, n)` by finitely many unit balls centred in it. -/
theorem exists_lintegral_weightedApproxDensity_le {γ : ℝ} {h : ℝ → ℂ → ℝ}
    {n β C : ℝ}
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ k : ℕ, ∫⁻ x, weightedApproxDensity γ h f k x ≤ M := by
  obtain ⟨t, hts, htfin, htcov⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : ℂ) n) one_pos
  refine ⟨ENNReal.ofReal K * ((htfin.toFinset.card : ℝ≥0∞) * ENNReal.ofReal C),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top), fun k => ?_⟩
  have hsupp : Function.support (weightedApproxDensity γ h f k) ⊆ closedBall (0 : ℂ) n := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_contra hxn
    exact hx (weightedApproxDensity_eq_zero (hfn x (not_le.1 hxn)))
  have hdens : ∀ x, weightedApproxDensity γ h f k x ≤ ENNReal.ofReal K *
      ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) x)) := fun x =>
    mul_le_mul' (ENNReal.ofReal_le_ofReal (hfK x).2) le_rfl
  have hball' : LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k)
      (closedBall (0 : ℂ) n) ≤ (htfin.toFinset.card : ℝ≥0∞) * ENNReal.ofReal C := by
    calc LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (closedBall (0 : ℂ) n)
        ≤ LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k)
            (⋃ x ∈ htfin.toFinset, ball x 1) := by
          refine measure_mono (htcov.trans ?_)
          intro y hy
          simp only [mem_iUnion, Finite.mem_toFinset] at hy ⊢
          exact hy
      _ ≤ ∑ x ∈ htfin.toFinset, LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k)
            (ball x 1) := measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ htfin.toFinset, ENNReal.ofReal C := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hxn : ‖x‖ ≤ n := mem_closedBall_zero_iff.1 (hts (htfin.mem_toFinset.1 hx))
          have := hball x (by linarith) 1 one_pos le_rfl k
          simpa using this
      _ = (htfin.toFinset.card : ℝ≥0∞) * ENNReal.ofReal C := by simp
  calc ∫⁻ x, weightedApproxDensity γ h f k x
      = ∫⁻ x in closedBall (0 : ℂ) n, weightedApproxDensity γ h f k x :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ ∫⁻ x in closedBall (0 : ℂ) n, ENNReal.ofReal K *
          ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
            Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) x)) := lintegral_mono hdens
    _ = ENNReal.ofReal K * LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k)
          (closedBall (0 : ℂ) n) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        unfold LatticeProb.LQG.lqgApprox
        rw [withDensity_apply _ measurableSet_closedBall]
    _ ≤ _ := mul_le_mul' le_rfl hball'

theorem enorm_toReal_le_self (x : ℝ≥0∞) : ‖x.toReal‖ₑ ≤ x := by
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/-- **Uniform second moment under the disc law.**  Under the hypotheses of
`exists_green_bound_weightedApproxDensity`, the occupation integrals
`X_k = (∫_{(0,1]} f ρ_k (b_s) ds)` of the approximating clocks satisfy
`∫ ‖X_k‖² d(ballLaw R) ≤ B` for a constant `B` independent of `k`. -/
theorem exists_lintegral_sq_windowOcc_ballLaw_le {γ : ℝ} {h : ℝ → ℂ → ℝ}
    (hmeas : ∀ k : ℕ, Measurable (h (LatticeProb.LQG.dyadicScale k)))
    {n β C : ℝ} (hβ : 0 < β) (hC0 : 0 < C)
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Measurable f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) (R : ℝ) :
    ∃ B : ℝ≥0, ∀ k : ℕ,
      ∫⁻ b, ‖(windowOcc (weightedApproxDensity γ h f k) b).toReal‖ₑ ^ 2 ∂ballLaw R ≤ B := by
  obtain ⟨U, hU, hUb⟩ := exists_green_bound_weightedApproxDensity hmeas hβ hC0 hball hf hfK hfn
  obtain ⟨M, hM, hMb⟩ := exists_lintegral_weightedApproxDensity_le hball hfK hfn
  have hfin : 2 * (U * M) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hU hM)
  refine ⟨(2 * (U * M)).toNNReal, fun k => ?_⟩
  have hgm := measurable_weightedApproxDensity (γ := γ) (h := h) (k := k) hf (hmeas k)
  have hn0 : ∀ y : ℂ, n < ‖y‖ → weightedApproxDensity γ h f k y = 0 := fun y hy =>
    weightedApproxDensity_eq_zero (hfn y hy)
  have hXm : Measurable fun b => (windowOcc (weightedApproxDensity γ h f k) b).toReal :=
    (measurable_windowOcc hgm).ennreal_toReal
  rw [ENNReal.coe_toNNReal hfin]
  calc ∫⁻ b, ‖(windowOcc (weightedApproxDensity γ h f k) b).toReal‖ₑ ^ 2 ∂ballLaw R
      = ∫⁻ z in ball (0 : ℂ) R,
          ∫⁻ b, ‖(windowOcc (weightedApproxDensity γ h f k) b).toReal‖ₑ ^ 2 ∂planarLaw z := by
        unfold ballLaw
        exact Measure.lintegral_bind measurable_planarLaw.aemeasurable
          ((hXm.enorm.pow_const 2).aemeasurable)
    _ ≤ ∫⁻ z in ball (0 : ℂ) R, ∫⁻ b, windowOcc (weightedApproxDensity γ h f k) b ^ 2
          ∂planarLaw z :=
        lintegral_mono fun z => lintegral_mono fun b =>
          pow_le_pow_left' (enorm_toReal_le_self _) 2
    _ ≤ ∫⁻ z, ∫⁻ b, windowOcc (weightedApproxDensity γ h f k) b ^ 2 ∂planarLaw z :=
        setLIntegral_le_lintegral _ _
    _ ≤ 2 * (U * ∫⁻ x, weightedApproxDensity γ h f k x) :=
        lintegral_lintegral_windowOcc_sq_le hgm hn0 (fun y hy => hUb k y hy)
    _ ≤ 2 * (U * M) := mul_le_mul' le_rfl (mul_le_mul' le_rfl (hMb k))

end MatedCRT.FirstPass.Derived

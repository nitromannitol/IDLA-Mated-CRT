import MatedCRT.Steps.Sec2.LQGMeasureProperties
import LatticeProb.Analysis.CircleAverageUniformLimit
import LatticeProb.LQG.MassFunctional

/-!
# Fact 2.2 III (Weyl scaling) and the circle average approximations of the LQG measure

`μ_h` is, by definition, the vague limit along `ε = 2⁻ᵏ` of `ε^{γ²/2} e^{γ h_ε(z)} dz` (`HarmonicBalls.lqgApprox`,
eq:measure-lim, line 468). The circle average of `h + f` is `h_ε + f_ε`, so the approximations of `h + f` are those of
`h` multiplied by the continuous densities `e^{γ f_ε}`, which converge to `e^{γ f}` uniformly on compact sets. A
uniformly convergent family of continuous weights passes through the vague limit (the masses of compact sets stay
bounded). This gives Fact 2.2 III (`lqgMeasureWeylScalingPart`, "immediate from the definition", line 492), and the
first half of Fact 2.2 I (local finiteness, part of the definition).
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The integral against a measure with a nonnegative measurable density `D`. -/
theorem integral_withDensity_ofReal {X : Type*} [MeasurableSpace X] {ν : Measure X} {D : X → ℝ}
    (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x) (g : X → ℝ) :
    ∫ x, g x ∂(ν.withDensity fun x => ENNReal.ofReal (D x)) = ∫ x, D x * g x ∂ν :=
  LatticeProb.CircleAverageUniformLimit.integral_withDensity_ofReal hD hD0 g

/-- The circle average approximation as a Lebesgue integral. -/
theorem integral_lqgApprox {γ ε : ℝ} (hε : 0 ≤ ε) {H : ℝ → ℂ → ℝ} (hH : Measurable (H ε)) (g : ℂ → ℝ) :
    ∫ z, g z ∂lqgApprox γ H ε = ∫ z, ε ^ (γ ^ 2 / 2) * Real.exp (γ * H ε z) * g z := by
  unfold lqgApprox
  exact integral_withDensity_ofReal (by fun_prop)
    (fun z => mul_nonneg (Real.rpow_nonneg hε _) (Real.exp_pos _).le) g

/-- The circle average approximation of a field whose circle averages at radius `ε` are continuous is locally finite. -/
theorem isLocallyFiniteMeasure_lqgApprox {γ ε : ℝ} {H : ℝ → ℂ → ℝ} (hH : Continuous (H ε)) :
    IsLocallyFiniteMeasure (lqgApprox γ H ε) := by
  unfold lqgApprox
  exact IsLocallyFiniteMeasure.withDensity_ofReal (μ := volume) (by fun_prop)

theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := pow_pos (by norm_num) k

theorem tendsto_dyadicScale : Tendsto dyadicScale atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The circle average of a continuous function is continuous in the centre. -/
theorem continuous_circleAverage_center {f : ℂ → ℝ} (hf : Continuous f) (R : ℝ) :
    Continuous fun c => Real.circleAverage f c R :=
  (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hf).comp
    (continuous_const.prodMk continuous_id)

/-- The circle averages `f_r` of a continuous `f` converge to `f` uniformly on compact sets as `r → 0`. -/
theorem tendstoUniformlyOn_circleAverage {f : ℂ → ℝ} (hf : Continuous f) {K : Set ℂ} (hK : IsCompact K)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    TendstoUniformlyOn (fun k z => Real.circleAverage f z (r k)) f atTop K := by
  have h := LatticeProb.Gauss.Section6.tendstoUniformlyOn_circleAverage hf hK
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp (hr.prodMap tendsto_id)

/-- Uniform convergence on a compact set is preserved by composition with a continuous function. -/
theorem TendstoUniformlyOn.comp_continuous_left {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hv : ContinuousOn v K) (h : TendstoUniformlyOn u v atTop K) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    TendstoUniformlyOn (fun k z => φ (u k z)) (fun z => φ (v z)) atTop K :=
  LatticeProb.CircleAverageUniformLimit.TendstoUniformlyOn.comp_continuous_left hK hv h hφ

/-- **Weights through a vague limit.** If `ν_k → m` vaguely (against continuous compactly supported functions) and
continuous weights `F_k` converge to a continuous `F` uniformly on compact sets, then `F_k ν_k → F m` vaguely. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn {ν : ℕ → Measure ℂ} {m : Measure ℂ}
    [∀ k, IsLocallyFiniteMeasure (ν k)]
    (hν : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k => ∫ z, g z ∂ν k) atTop (𝓝 (∫ z, g z ∂m)))
    {F : ℂ → ℝ} {Fk : ℕ → ℂ → ℝ} (hF : Continuous F) (hFk : ∀ k, Continuous (Fk k))
    (hunif : ∀ K, IsCompact K → TendstoUniformlyOn Fk F atTop K)
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun k => ∫ z, Fk k z * g z ∂ν k) atTop (𝓝 (∫ z, F z * g z ∂m)) :=
  LatticeProb.CircleAverageUniformLimit.tendsto_integral_mul_of_tendstoUniformlyOn hν hF hFk hunif hg hgc

/-- **Weyl scaling for a vague dyadic limit.** If `m` is the LQG limit of a field `H` whose circle averages at
positive radii are continuous, then for every continuous `f`, `e^{γ f} m` is the LQG limit of `H + f`. -/
theorem isLQGLimit_addCircleAverage {γ : ℝ} {H : ℝ → ℂ → ℝ} {m : Measure ℂ} (hm : IsLQGLimit γ H m)
    (hH : ∀ ε, 0 < ε → Continuous (H ε)) {f : ℂ → ℝ} (hf : Continuous f) :
    IsLQGLimit γ (addCircleAverage H f) (m.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) := by
  have := hm.isLocallyFiniteMeasure
  have hF : Continuous fun x => Real.exp (γ * f x) := by fun_prop
  refine ⟨IsLocallyFiniteMeasure.withDensity_ofReal hF, fun g hg hgc => ?_⟩
  have hcA : ∀ k, Continuous fun z => Real.circleAverage f z (dyadicScale k) :=
    fun k => continuous_circleAverage_center hf _
  have hL : ∀ k, ∫ z, g z ∂lqgApprox γ (addCircleAverage H f) (dyadicScale k) =
      ∫ z, Real.exp (γ * Real.circleAverage f z (dyadicScale k)) * g z ∂lqgApprox γ H (dyadicScale k) := by
    intro k
    have hc1 := hH _ (dyadicScale_pos k)
    have hc2 := hcA k
    rw [integral_lqgApprox (dyadicScale_pos k).le (hc1.add hc2).measurable,
      integral_lqgApprox (dyadicScale_pos k).le hc1.measurable]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [addCircleAverage, mul_add, Real.exp_add]
    ring
  have hR : ∫ z, g z ∂(m.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) =
      ∫ z, Real.exp (γ * f z) * g z ∂m :=
    integral_withDensity_ofReal hF.measurable (fun _ => (Real.exp_pos _).le) g
  rw [hR]
  simp only [hL]
  have : ∀ k, IsLocallyFiniteMeasure (lqgApprox γ H (dyadicScale k)) :=
    fun k => isLocallyFiniteMeasure_lqgApprox (hH _ (dyadicScale_pos k))
  exact tendsto_integral_mul_of_tendstoUniformlyOn (ν := fun k => lqgApprox γ H (dyadicScale k))
    (Fk := fun k z => Real.exp (γ * Real.circleAverage f z (dyadicScale k)))
    (F := fun z => Real.exp (γ * f z)) hm.tendsto_integral hF
    (fun k => Real.continuous_exp.comp (continuous_const.mul (hcA k)))
    (fun K hK => TendstoUniformlyOn.comp_continuous_left (φ := fun x => Real.exp (γ * x))
      (u := fun k z => Real.circleAverage f z (dyadicScale k)) (v := f) hK hf.continuousOn
      (tendstoUniformlyOn_circleAverage hf hK tendsto_dyadicScale) (by fun_prop)) hg hgc

/-- A.s. the circle averages of the quantum cone at a positive radius are continuous in the centre. -/
theorem ae_continuous_circle {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ ε, 0 < ε → Continuous (hcirc ω ε) := by
  filter_upwards [hcone.ae_continuousOn_circle] with ω hω ε hε
  have hpair : ContinuousOn (fun z : ℂ => ((ε, z) : ℝ × ℂ)) univ := by fun_prop
  exact continuousOn_univ.mp (hω.comp hpair (fun z _ => ⟨hε, mem_univ z⟩))

/-- **Fact 2.2 III** (Weyl scaling), from the definition of the LQG measure. -/
theorem lqgMeasureWeylScalingPart : LQGMeasureWeylScalingPart := by
  intro γ _ _ Ω _ P hC hcirc μ hμ
  obtain ⟨-, hcone, hlqg⟩ := hμ
  filter_upwards [hlqg, ae_continuous_circle hcone] with ω hω hcont f hf
  exact isLQGLimit_addCircleAverage hω hcont hf

/-- **Fact 2.2 I, locally finite half**, from the definition of the LQG measure. -/
theorem ae_isLocallyFiniteMeasure {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsConeField γ P hC hcirc μ) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
  filter_upwards [hμ.2.2] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- **Fact 2.2 I** from its non-atomic half (cited). -/
theorem lqgMeasureRadonPart_of_nonAtomic (h : LQGMeasureNonAtomicPart) : LQGMeasureRadonPart := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hμ
  filter_upwards [ae_isLocallyFiniteMeasure hμ, h γ hγ hγ2 Ω P hC hcirc μ hμ] with ω h1 h2
  exact ⟨h1, h2⟩

end MatedCRT.LQGMeasure

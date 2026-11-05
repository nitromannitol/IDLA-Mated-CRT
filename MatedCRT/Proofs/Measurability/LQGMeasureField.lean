import MatedCRT.Proofs.Measurability.FieldCircle
import MatedCRT.Proofs.Measurability.VagueMeasurable
import MatedCRT.Proofs.Measurability.GoodScale

/-!
# The LQG measure is determined by the field

`lqgMeasureFieldMeasurableStep : LQGMeasureFieldMeasurableStep 𝒮` (eq:measure-lim, line 470): the `γ`-LQG measure
`μ_h` of the environment is almost surely equal to a `σ(h)`-measurable random measure.

Proof. The approximating measures `ε^{γ²/2} e^{γ h_ε(z)} dz`, `ε = 2^{-n}`, are almost surely equal, for all `n` at once,
to the measures built from the jointly `σ(h) ⊗ 𝓑(ℂ)`-measurable version `dyadicCircleVersion` of the circle averages
(`ae_dyadicCircleVersion_eq`, from the convergence of the pairings with mollified circle measures to the circle
averages); these are `σ(h)`-measurable random measures with `σ(h)`-measurable integrals; their vague limit has a
`σ(h)`-measurable choice (`exists_measurable_vagueLimit`), which is `μ_h` wherever `μ_h` is the vague limit
(`IsLQGLimit`), i.e. almost surely.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT
namespace LQGMeasureField

open FieldCircle VagueWholePlane

section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma measurable_withDensity_ofReal {d : Ω → ℂ → ℝ} (hd : Measurable (Function.uncurry d)) :
    Measurable fun ω => (volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z) :=
  measurable_withDensity (ENNReal.measurable_ofReal.comp hd)

lemma measurable_integral_withDensity_ofReal {d : Ω → ℂ → ℝ} (hd : Measurable (Function.uncurry d))
    (hd0 : ∀ ω z, 0 ≤ d ω z) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun ω => ∫ z, f z ∂((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z)) := by
  have e : ∀ ω, ∫ z, f z ∂((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z)) =
      ∫ z, d ω z * f z := by
    intro ω
    have hm : Measurable fun z => Real.toNNReal (d ω z) := (hd.comp measurable_prodMk_left).real_toNNReal
    rw [show (fun z => ENNReal.ofReal (d ω z)) = fun z => ((Real.toNNReal (d ω z) : ℝ≥0) : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hm]
    congr 1
    funext z
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hd0 ω z), smul_eq_mul]
  simp_rw [e]
  exact (hd.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

end Generic

lemma withDensity_ofReal_lt_top {g : ℂ → ℝ} (hg : Continuous g) {K : Set ℂ} (hK : IsCompact K) :
    ((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (g z)) K < ∞ := by
  rw [withDensity_apply _ hK.measurableSet]
  exact (hg.continuousOn.integrableOn_compact hK).lintegral_lt_top

variable {Ω : Type} [MeasurableSpace Ω]

/-- The density `2^{-nγ²/2} e^{γ h_{2^{-n}}(z)}` computed with the `σ(h)`-measurable version of the circle averages. -/
def approxDensity (γ : ℝ) (S : MatedCRTEnv Ω) (n : ℕ) (ω : Ω) (z : ℂ) : ℝ :=
  dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * dyadicCircleVersion S n ω z)

lemma approxDensity_nonneg (γ : ℝ) (S : MatedCRTEnv Ω) (n : ℕ) (ω : Ω) (z : ℂ) :
    0 ≤ approxDensity γ S n ω z :=
  mul_nonneg (Real.rpow_nonneg (by unfold dyadicScale; positivity) _) (Real.exp_pos _).le

lemma measurable_approxDensity (γ : ℝ) (S : MatedCRTEnv Ω) (n : ℕ) :
    Measurable[S.fieldSigma.prod (inferInstance : MeasurableSpace ℂ)] (Function.uncurry (approxDensity γ S n)) :=
  measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (measurable_dyadicCircleVersion S n)))

/-- **The LQG measure is almost surely equal to a `σ(h)`-measurable random measure** (eq:measure-lim, line 470). -/
theorem lqgMeasureFieldMeasurableStep (𝒮 : SpaceFillingSLEModel) : LQGMeasureFieldMeasurableStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS
  let ν : ℕ → Ω → Measure ℂ := fun n ω =>
    (volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (approxDensity γ S n ω z)
  have hν : ∀ n, Measurable[S.fieldSigma] (ν n) := fun n =>
    measurable_withDensity_ofReal (mΩ := S.fieldSigma) (measurable_approxDensity γ S n)
  have hint : ∀ n (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      Measurable[S.fieldSigma] fun ω => ∫ z, f z ∂(ν n ω) := fun n f hf _ =>
    measurable_integral_withDensity_ofReal (mΩ := S.fieldSigma) (measurable_approxDensity γ S n)
      (approxDensity_nonneg γ S n) hf.measurable
  obtain ⟨μ', hμ', hlim⟩ := exists_measurable_vagueLimit (mΩ := S.fieldSigma) ν hν hint
  refine ⟨μ', hμ', ?_⟩
  have hLQG : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  filter_upwards [ae_dyadicCircleVersion_eq hS, hLQG, hS.isQuantumCone.ae_continuousOn_circle] with ω h1 h2 h3
  have hdens : ∀ n z, approxDensity γ S n ω z =
      dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * S.hcirc ω (dyadicScale n) z) := fun n z => by
    rw [approxDensity, h1 n z]
    rfl
  have hνeq : ∀ n, ν n ω = lqgApprox γ (S.hcirc ω) (dyadicScale n) := by
    intro n
    simp only [ν, hdens]
    rfl
  refine hlim ω (S.μ ω) (fun K hK => Eventually.of_forall fun n => ?_) ⟨?_, fun K hK _ => ?_, fun f hf hfc _ => ?_⟩
  · have hc : Continuous fun w => S.hcirc ω (dyadicScale n) w := by
      rw [← continuousOn_univ]
      exact h3.comp (continuous_const.prodMk continuous_id).continuousOn
        fun w _ => ⟨mem_Ioi.2 (show (0 : ℝ) < 2⁻¹ ^ n by positivity), mem_univ _⟩
    simp only [ν, hdens]
    exact withDensity_ofReal_lt_top (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))) hK
  · rw [compl_univ, measure_empty]
  · have := h2.isLocallyFiniteMeasure
    exact hK.measure_lt_top
  · simp_rw [hνeq]
    exact h2.tendsto_integral f hf hfc

end LQGMeasureField
end MatedCRT

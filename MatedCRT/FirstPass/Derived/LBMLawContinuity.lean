import MatedCRT.FirstPass.Derived.LBMLawContinuityAt
import MatedCRT.FirstPass.Derived.LQGApproxPathKernel

/-!
# Weak continuity in the starting point of the law of the time-changed path

Let `F` be an LQG clock of planar Brownian motion from every start (`IsLQGClock`) that is almost
surely a time-change clock, with time-changed path map `Φ = lbmContinuousPath F`, for circle
averages continuous at every dyadic radius and satisfying, for every `R > 0`, the stopped heat bound
`E^z ∫_0^{t ∧ τ_{B(0, R+1)}} ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds ≤ C t^β` (`β > 0`) for all starts
`|z| ≤ R`.

* `tendsto_planarBrownianPathLaw_lbmContinuousPath_nhds`: the law of `Φ` under planar Brownian
  motion from `z` converges weakly to the law from `z₀` as `z → z₀`. By the Portmanteau theorem
  for the local uniform metric `dUnif` (whose topology is the compact-open topology) it suffices to
  test bounded Lipschitz functions, which after an affine normalization are bounded by `1`.
* `continuous_planarBrownianPathLaw_lbmContinuousPath`: the law of `Φ` is weakly continuous in the
  starting point.
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess Filter Topology
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ}

/-- Affine normalization of an integral against a probability measure:
`∫ g = D ∫ (g - c) / D + c` for `D ≠ 0`. -/
theorem integral_eq_mul_integral_sub_div_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Integrable g μ) (c : ℝ) {D : ℝ} (hD : D ≠ 0) :
    ∫ x, g x ∂μ = D * ∫ x, (g x - c) / D ∂μ + c := by
  rw [integral_div, integral_sub hg (integrable_const c), integral_const, probReal_univ,
    one_smul, mul_div_cancel₀ _ hD]
  ring

/-- **Weak continuity at a point.** Under the hypotheses of
`tendsto_integral_lbmContinuousPath_nhds` (with `|z₀| < R`), the law under planar Brownian motion
from `z` of the time-changed path `Φ` converges weakly to the law from `z₀` as `z → z₀`. -/
theorem tendsto_planarBrownianPathLaw_lbmContinuousPath_nhds {z0 : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ z, ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {R β C : ℝ} (hR : ‖z0‖ < R)
    (hβ : 0 < β)
    (hheat : ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (Metric.ball (0 : ℂ) (R + 1)) b).toReal),
          ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
            Real.exp (γ * hε (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
        ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β)) :
    Tendsto (fun z => planarBrownianPathLaw z (lbmContinuousPath F)
        (aemeasurable_lbmContinuousPath (hF z) (hFc z) hcont)) (𝓝 z0)
      (𝓝 (planarBrownianPathLaw z0 (lbmContinuousPath F)
        (aemeasurable_lbmContinuousPath (hF z0) (hFc z0) hcont))) := by
  let m : PseudoMetricSpace (ContinuousPath ℂ) :=
    (LatticeProb.dUnifMetricSpace (E := ℂ)).toPseudoMetricSpace
  have hOM : @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _
        (@PseudoEMetricSpace.toUniformSpace _ m.toPseudoEMetricSpace)) _ :=
    (inferInstance : OpensMeasurableSpace (ContinuousPath ℂ))
  refine (@tendsto_iff_forall_lipschitz_integral_tendsto ℂ (ContinuousPath ℂ) _
    m.toPseudoEMetricSpace hOM (𝓝 z0) _ _ _).2 ?_
  rintro f ⟨C0, hC0⟩ ⟨K, hK⟩
  have hfL : ∀ x y, |f x - f y| ≤ (K : ℝ) * LatticeProb.dUnif x y := fun x y => by
    have := @LipschitzWith.dist_le_mul _ _ m _ K f hK x y
    rwa [Real.dist_eq] at this
  have hfc : Continuous f := @LipschitzWith.continuous _ _ m.toPseudoEMetricSpace _ K f hK
  let p0 : ContinuousPath ℂ := ContinuousMap.const _ 0
  have hC0' : 0 ≤ C0 := (dist_nonneg).trans (hC0 p0 p0)
  have hD : (0 : ℝ) < C0 + 1 := by linarith
  set G : ContinuousPath ℂ → ℝ := fun x => (f x - f p0) / (C0 + 1) with hGdef
  have hGc : Continuous G := (hfc.sub continuous_const).div_const _
  have hG1 : ∀ x, |G x| ≤ 1 := fun x => by
    rw [hGdef, abs_div, abs_of_pos hD, div_le_one hD]
    have := hC0 x p0
    rw [Real.dist_eq] at this
    linarith
  have hGL : ∀ x y, |G x - G y| ≤ (K / (C0 + 1)) * LatticeProb.dUnif x y := fun x y => by
    rw [hGdef, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hD, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hD]
    exact hfL x y
  have hlim := tendsto_integral_lbmContinuousPath_nhds hF hFc hcont hR hβ hheat hGc hG1
    (div_nonneg K.coe_nonneg hD.le) hGL
  -- integrals against the laws are expectations of `f ∘ Φ`
  have hint : ∀ z, ∫ q, f q ∂(planarBrownianPathLaw z (lbmContinuousPath F)
      (aemeasurable_lbmContinuousPath (hF z) (hFc z) hcont) : Measure (ContinuousPath ℂ)) =
      (C0 + 1) * ∫ b, G (lbmContinuousPath F b) ∂planarBrownianMotion z + f p0 := fun z => by
    have hmap : ∫ q, f q ∂(planarBrownianPathLaw z (lbmContinuousPath F)
        (aemeasurable_lbmContinuousPath (hF z) (hFc z) hcont) : Measure (ContinuousPath ℂ)) =
        ∫ b, f (lbmContinuousPath F b) ∂planarBrownianMotion z := by
      show ∫ q, f q ∂(Measure.map (lbmContinuousPath F) (planarBrownianMotion z)) = _
      exact integral_map (aemeasurable_lbmContinuousPath (hF z) (hFc z) hcont)
        hfc.aestronglyMeasurable
    have hfi : Integrable (fun b => f (lbmContinuousPath F b)) (planarBrownianMotion z) :=
      Integrable.of_bound ((hfc.measurable.comp_aemeasurable
        (aemeasurable_lbmContinuousPath (hF z) (hFc z) hcont)).aestronglyMeasurable)
        (|f p0| + C0) (ae_of_all _ fun b => by
          have := hC0 (lbmContinuousPath F b) p0
          rw [Real.dist_eq] at this
          rw [Real.norm_eq_abs]
          calc |f (lbmContinuousPath F b)|
              = |(f (lbmContinuousPath F b) - f p0) + f p0| := by rw [sub_add_cancel]
            _ ≤ |f (lbmContinuousPath F b) - f p0| + |f p0| := abs_add_le _ _
            _ ≤ |f p0| + C0 := by linarith)
    rw [hmap, integral_eq_mul_integral_sub_div_add hfi (f p0) hD.ne']
  simp only [hint]
  exact (hlim.const_mul (C0 + 1)).add_const (f p0)

/-- **Weak continuity of the law of the time-changed path.** Let `F` be an LQG clock of planar
Brownian motion from every start that is almost surely a time-change clock, for circle averages
continuous at every dyadic radius and satisfying, for every `R > 0`, the stopped heat bound with
some exponent `β > 0` for all starts `|z| ≤ R`. Then `z ↦ Law^z(Φ)` is continuous for the topology
of weak convergence. -/
theorem continuous_planarBrownianPathLaw_lbmContinuousPath
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ z, ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n)))
    (hheat : ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
        ∫⁻ b, (∫⁻ s in Ioc 0 (min t
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) (R + 1)) b).toReal),
            ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * hε (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
          ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β))
    (hg : ∀ z, AEMeasurable (lbmContinuousPath F) (planarBrownianMotion z)) :
    Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath F) (hg z) := by
  refine continuous_iff_continuousAt.2 fun z0 => ?_
  obtain ⟨β, C, hβ, -, hb⟩ := hheat (‖z0‖ + 1) (by positivity)
  exact tendsto_planarBrownianPathLaw_lbmContinuousPath_nhds hF hFc hcont
    (lt_add_one _) hβ hb

end MatedCRT.FirstPass.Derived

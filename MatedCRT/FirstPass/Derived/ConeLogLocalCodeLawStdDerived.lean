import MatedCRT.FirstPass.Frozen.S2g
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.LPBridge.WholePlaneContinuousVersion
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneRestrictedLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.WholePlaneLQGMeasurable
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.Steps.Sec11.ScalePowerBounds

/-!
# The standard Borel whole-plane model of the local law of the quantum cone

`FrozenConeLogLocalCodeLawStd` (`FirstPass/Frozen/S2g.lean`): the moment vectors, against continuous test
functions with compact support in the unit disk, of the `γ`-LQG measure of a quantum cone have the law of those of
the `γ`-LQG measure of `h^ℂ - γ log |·|`, for a standard Borel whole-plane model with a measurable measure map.

The model is the canonical sample space `ℕ → ℝ` of a whole-plane GFF with continuous circle averages
(`wholePlaneGFF_exists_nat_continuous`) with a measurable version of its LQG measure of insertion `γ`.  The law
identity is the equality in law of the restrictions to `B_1` of the two LQG measures
(`coneWholePlaneRestrictedLQGLawStep_of_fieldLaw`, from the field law `coneWholePlaneFieldLawStep_holds` and the
locality of the LQG measure), together with the fact that the moment vector against a test function supported in
the unit disk only sees the restriction to the unit disk.
-/

open MeasureTheory HarmonicBalls Set

namespace MatedCRT.FirstPass.Derived

/-- The moment vector of a measure against test functions vanishing outside the unit disk only depends on the
restriction of the measure to the unit disk. -/
theorem momentVec_restrict_ball {φs : ℕ → ℂ → ℝ}
    (hφ : ∀ k, tsupport (φs k) ⊆ Metric.ball (0 : ℂ) 1) (ν : Measure ℂ) :
    momentVec φs (ν.restrict (Metric.ball (0 : ℂ) 1)) = momentVec φs ν := by
  funext k
  have hzero : ∀ x : ℂ, x ∉ Metric.ball (0 : ℂ) 1 → φs k x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ k h)
  have hs : ∀ g : ℂ → ℝ, (∀ x, x ∉ Metric.ball (0 : ℂ) 1 → g x = 0) →
      ∫⁻ x in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (g x) ∂ν = ∫⁻ x, ENNReal.ofReal (g x) ∂ν := by
    intro g hg
    refine setLIntegral_eq_of_support_subset ?_
    intro x hx
    by_contra hxs
    exact hx (by simp [hg x hxs])
  simp only [momentVec, intG]
  rw [hs (φs k) (hzero)]
  rw [hs (fun x => -φs k x) (fun x hx => by simp [hzero x hx])]

/-- **The local law of the quantum cone, standard Borel form (`FrozenConeLogLocalCodeLawStd`) is a theorem.** -/
theorem frozenConeLogLocalCodeLawStd_holds : FrozenConeLogLocalCodeLawStd := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨P₁, hC₁, c₁, hP₁, hh, -, -⟩ := MatedCRT.Field.wholePlaneGFF_exists_nat_continuous
  have hlt : γ < lqgQ γ := gamma_lt_lqgQ hγ hγ2
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistence_derived P₁ γ γ hC₁ c₁ hh hγ hγ2 hlt
  obtain ⟨μ', hμ'm, hμ'eq⟩ : AEMeasurable μ₀ P₁ := aemeasurable_wholePlaneLQGMeasure hh hμ₀
  have hμ' : IsLQGMeasureOfField P₁ γ γ c₁ μ' := by
    unfold IsLQGMeasureOfField IsLQGMeasure at hμ₀ ⊢
    filter_upwards [hμ₀, hμ'eq] with ω h1 h2
    rw [← h2]
    exact h1
  have hlaw := MatedCRT.coneWholePlaneRestrictedLQGLawStep_of_fieldLaw
    MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds γ hγ hγ2 Ω P hC hcirc μ hcone
    (ℕ → ℝ) P₁ hC₁ c₁ μ' hP₁ hh hμ'
  refine ⟨ℕ → ℝ, inferInstance, inferInstance, P₁, hC₁, c₁, μ', hP₁, hμ'm, hh, hμ', ?_⟩
  intro φs hφs
  have hmeas : ∀ k, Measurable (φs k) := fun k => (hφs k).1.measurable
  have hsupp : ∀ k, tsupport (φs k) ⊆ Metric.ball (0 : ℂ) 1 := fun k => (hφs k).2.2
  have hmv : Measurable (momentVec φs) := measurable_momentVec hmeas
  have h1 : (fun ω => momentVec φs (μ ω)) =
      momentVec φs ∘ (fun ω => (μ ω).restrict (Metric.ball (0 : ℂ) 1)) := by
    funext ω
    exact (momentVec_restrict_ball hsupp (μ ω)).symm
  have h2 : (fun ω' => momentVec φs (μ' ω')) =
      momentVec φs ∘ (fun ω' => (μ' ω').restrict (Metric.ball (0 : ℂ) 1)) := by
    funext ω'
    exact (momentVec_restrict_ball hsupp (μ' ω')).symm
  rw [h1, h2, ← AEMeasurable.map_map_of_aemeasurable hmv.aemeasurable hlaw.aemeasurable_fst,
    ← AEMeasurable.map_map_of_aemeasurable hmv.aemeasurable hlaw.aemeasurable_snd, hlaw.map_eq]

end MatedCRT.FirstPass.Derived

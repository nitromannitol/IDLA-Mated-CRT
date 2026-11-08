import MatedCRT.Proofs.Sec1.EnvironmentScaling.AreaScaling
import MatedCRT.Proposed.SheffieldWang2016
import MatedCRT.Proposed.DuplantierSheffieldCoordinate2011

/-!
# All-scale area limits from local Dirichlet decompositions

The local decomposition and the dyadic zero-boundary measures are hypotheses.
The Sheffield--Wang input remains staged and explicit. This bridges those
hypotheses to the random-radius identity in `AreaScaling`, without asserting
a cone all-scale theorem. See `env-steps.tex`, lines 715--730.
-/

open MeasureTheory Filter Set HarmonicBalls
open scoped Topology

namespace MatedCRT.Sec1

/-- Sheffield--Wang and an admissible-circle decomposition give the local
all-scale limits. The continuous remainder may depend on the Dirichlet field. -/
theorem ae_local_limits_of_dirichlet_decomposition
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set ℂ) (hD : IsOpen D) (hDne : D ≠ univ)
    (hDsc : SimplyConnectedSpace D) (hDb : Bornology.IsBounded D)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ2 : γ < 2)
    (hSW : SheffieldWangCircleAverageAllScaleStmt.{0})
    (H : Ω → ℝ → ℂ → ℝ) (h : Ω → (ℂ → ℝ) → ℝ)
    (hc : Ω → ℝ → ℂ → ℝ) (m : Ω → Measure ℂ)
    (hGFF : IsDirichletGFF P D h hc)
    (hext : ∀ ω r z, ¬ Metric.closedBall z r ⊆ D → hc ω r z = 0)
    (hdyad : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (m ω) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
        Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (hc ω) (dyadicScale n)))
          atTop (𝓝 (∫ z, f z ∂(m ω))))
    (hdecomp : ∀ᵐ ω ∂P, ∃ v : ℂ → ℝ, ContinuousOn v D ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ D →
        H ω r z = addCircleAverage (hc ω) v r z) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ D → ∃ l : ℝ,
        Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ (H ω) r)) (𝓝[>] 0) (𝓝 l) := by
  have hall := hSW Ω P D h hc m γ hD hDne hDsc hDb hGFF hγ hγ2 hext hdyad
  filter_upwards [hdyad, hGFF.continuous_circle, hall, hdecomp] with ω hm hcω hallω hdec
  obtain ⟨v, hv, heq⟩ := hdec
  intro f hf hfc hfD
  exact ⟨∫ z, f z * Real.exp (γ * v z) ∂(m ω),
    tendsto_lqgApprox_of_admissible_circle_decomposition hD hm.1 hcω hallω v hv heq f hf hfc hfD⟩

/-- On the canonical punctured-plane disks, same-space Dirichlet fields with
local dyadic measures and continuous remainders suffice for the random-radius
area identity, conditional on the staged Sheffield--Wang input. -/
theorem MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_dirichlet_decompositions
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (R : Ω → ℝ) {ν : Ω → Measure ℂ}
    (hR : ∀ᵐ ω ∂S.P, 0 < R ω)
    (hν : IsLQGMeasure S.P γ (fun ω => rescaledCircle γ (S.hcirc ω) (R ω) b) ν)
    (hν0 : ∀ᵐ ω ∂S.P, ν ω {0} = 0)
    (hSW : SheffieldWangCircleAverageAllScaleStmt.{0})
    (h : PuncturedPlaneDiskIndex → Ω → (ℂ → ℝ) → ℝ)
    (hc : PuncturedPlaneDiskIndex → Ω → ℝ → ℂ → ℝ)
    (m : PuncturedPlaneDiskIndex → Ω → Measure ℂ)
    (hGFF : ∀ i, IsDirichletGFF S.P (puncturedPlaneDisk i) (h i) (hc i))
    (hext : ∀ i ω r z, ¬ Metric.closedBall z r ⊆ puncturedPlaneDisk i → hc i ω r z = 0)
    (hdyad : ∀ i, ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (m i ω) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ puncturedPlaneDisk i →
        Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (hc i ω) (dyadicScale n)))
          atTop (𝓝 (∫ z, f z ∂(m i ω))))
    (hdecomp : ∀ i, ∀ᵐ ω ∂S.P, ∃ v : ℂ → ℝ,
      ContinuousOn v (puncturedPlaneDisk i) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ puncturedPlaneDisk i →
        S.hcirc ω r z = addCircleAverage (hc i ω) v r z) :
    ∀ᵐ ω ∂S.P, ν ω = rescaledMeasure (S.μ ω) (R ω) b := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_countable_local_limits_of_null
    hS hγ.ne' hb R hR hν hν0 puncturedPlaneDisk
    (fun i => (puncturedPlaneDisk_properties i).1) puncturedPlaneDisk_cover
  intro i
  exact ae_local_limits_of_dirichlet_decomposition S.P (puncturedPlaneDisk i)
    (puncturedPlaneDisk_properties i).1 (puncturedPlaneDisk_ne_univ i)
    (puncturedPlaneDisk_properties i).2.2.1 (puncturedPlaneDisk_properties i).2.1
    γ hγ.le hγ2 hSW S.hcirc (h i) (hc i) (m i) (hGFF i) (hext i) (hdyad i) (hdecomp i)

/-- The staged dyadic existence input supplies the local measures required by
`ae_rescaled_measure_eq_of_dirichlet_decompositions`. Both literature inputs
remain explicit, and the same-space circle decompositions are still required. -/
theorem MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_dirichlet_fields
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (R : Ω → ℝ) {ν : Ω → Measure ℂ}
    (hR : ∀ᵐ ω ∂S.P, 0 < R ω)
    (hν : IsLQGMeasure S.P γ (fun ω => rescaledCircle γ (S.hcirc ω) (R ω) b) ν)
    (hν0 : ∀ᵐ ω ∂S.P, ν ω {0} = 0)
    (hSW : SheffieldWangCircleAverageAllScaleStmt.{0})
    (hDS : MatedCRT.Proposed.DS11Prop11ZeroBoundaryMeasure)
    (h : PuncturedPlaneDiskIndex → Ω → (ℂ → ℝ) → ℝ)
    (hc : PuncturedPlaneDiskIndex → Ω → ℝ → ℂ → ℝ)
    (hGFF : ∀ i, IsDirichletGFF S.P (puncturedPlaneDisk i) (h i) (hc i))
    (hext : ∀ i ω r z, ¬ Metric.closedBall z r ⊆ puncturedPlaneDisk i → hc i ω r z = 0)
    (hdecomp : ∀ i, ∀ᵐ ω ∂S.P, ∃ v : ℂ → ℝ,
      ContinuousOn v (puncturedPlaneDisk i) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ puncturedPlaneDisk i →
        S.hcirc ω r z = addCircleAverage (hc i ω) v r z) :
    ∀ᵐ ω ∂S.P, ν ω = rescaledMeasure (S.μ ω) (R ω) b := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hex : ∀ i, ∃ m : Ω → Measure ℂ,
      ∀ᵐ ω ∂S.P, MatedCRT.Proposed.DS11IsLQGLimitInside
        (puncturedPlaneDisk i) γ (hc i ω) (m ω) := by
    intro i
    exact (hDS γ hγ.le hγ2 (puncturedPlaneDisk i)
      (puncturedPlaneDisk_properties i).1 (puncturedPlaneDisk_properties i).2.2.1
      (puncturedPlaneDisk_properties i).2.1 Ω S.P (h i) (hc i)
      hS.isProbabilityMeasure (hGFF i)).1
  choose m hm using hex
  apply MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_dirichlet_decompositions
    hS hγ hγ2 hb R hR hν hν0 hSW h hc m hGFF hext
  · intro i
    filter_upwards [hm i] with ω hω
    exact ⟨hω.isLocallyFiniteMeasure, hω.tendsto_integral⟩
  · exact hdecomp

end MatedCRT.Sec1

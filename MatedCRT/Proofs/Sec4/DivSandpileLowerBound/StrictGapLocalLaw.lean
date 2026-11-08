import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapFixedTime
import HarmonicBalls.Proofs.Sec5.CompactClusterMeasureLocality

/-! Fixed-time defect reduction using the law of the measure restricted to the disc. -/

namespace MatedCRT

open Set MeasureTheory Metric _root_.HarmonicBalls

/-- A compactly confined disc cluster depends only on the measure restricted
 to the disc, provided the two least supersolutions are admissible. -/
theorem cluster_eq_cluster_restrict_ball_of_compact
    {μ : Measure ℂ} {ρ t : ℝ} {z : ℂ} (hz : z ∈ ball 0 ρ)
    (hμ : leastSupersolution μ ρ z t ∈ supersolutions μ ρ z t)
    (hμr : leastSupersolution (μ.restrict (ball 0 ρ)) ρ z t ∈
      supersolutions (μ.restrict (ball 0 ρ)) ρ z t)
    (hcompact : closure (cluster μ ρ z t) ⊆ ball 0 ρ) :
    cluster μ ρ z t = cluster (μ.restrict (ball 0 ρ)) ρ z t := by
  apply cluster_eq_of_restrict_eq_of_closure_subset isOpen_ball Subset.rfl _ hz hμ hμr hcompact
  rw [Measure.restrict_restrict measurableSet_ball, inter_self]

/-- Fixed-time regularization defects are null when the shifted laws of the
measure restricted to the disc satisfy the fixed-time Tonelli hypotheses. -/
theorem ae_no_regularization_defect_of_restricted_shifted_measure_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) {ρ t γ : ℝ} {z : ℂ} (ht : 0 < t) (hγ : γ ≠ 0)
    (hz : z ∈ ball 0 ρ)
    (hvalid : ∀ᵐ ω ∂P,
      leastSupersolution (μ ω) ρ z t ∈ supersolutions (μ ω) ρ z t ∧
      leastSupersolution ((μ ω).restrict (ball 0 ρ)) ρ z t ∈
        supersolutions ((μ ω).restrict (ball 0 ρ)) ρ z t)
    (hopen : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      IsOpen (cluster ((μ ω).restrict (ball 0 ρ)) ρ z s))
    (hcompare : ∀ᵐ ω ∂P, ∀ s u : ℝ, 0 < s → s < u →
      closure (cluster ((μ ω).restrict (ball 0 ρ)) ρ z u) ⊆ ball 0 ρ →
      interior (closure (cluster ((μ ω).restrict (ball 0 ρ)) ρ z s)) ⊆
        cluster ((μ ω).restrict (ball 0 ρ)) ρ z u)
    (hB : MeasurableSet (confinedRegularizationDefect ρ t z))
    (hY : ∀ c : ℝ, AEMeasurable (fun ω =>
      ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 ρ)) P)
    (hjoint : MeasurableSet {p : Ω × ℝ |
      ENNReal.ofReal (Real.exp (γ * p.2)) • (μ p.1).restrict (ball 0 ρ) ∈
        confinedRegularizationDefect ρ t z})
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 ρ)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 ρ)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) ρ z t) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z t)) = cluster (μ ω) ρ z t := by
  have hlocal := ae_no_regularization_defect_of_shifted_measure_law P
    (fun ω => (μ ω).restrict (ball 0 ρ)) ht hγ hopen hcompare hB hY hjoint hlaw
  filter_upwards [hlocal, hvalid] with ω hlocal hvalid hcompact
  have heq := cluster_eq_cluster_restrict_ball_of_compact hz hvalid.1 hvalid.2 hcompact
  rw [heq] at hcompact ⊢
  exact hlocal hcompact

end MatedCRT

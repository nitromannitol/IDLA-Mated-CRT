import MatedCRT.Defs.DirichletGFF
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuousFieldMeasurable
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Joint measurability of Dirichlet circle averages -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls
open scoped NNReal

/-- On a region whose averaging disks lie in the field domain, a Dirichlet
GFF circle-average field has a jointly measurable version which agrees
simultaneously at every center almost surely. -/
theorem IsDirichletGFF.exists_jointlyMeasurable_circle
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {D U : Set ℂ}
    {h : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsDirichletGFF P D h hcirc) (ε : ℝ) (hε : 0 < ε)
    (hdisks : ∀ z ∈ U, Metric.closedBall z ε ⊆ D) :
    ∃ g : Ω × U → ℝ, Measurable g ∧
      ∀ᵐ ω ∂P, ∀ z : U, g (ω, z) = hcirc ω ε z := by
  apply exists_jointlyMeasurable_of_ae_continuous P (fun ω (z : U) => hcirc ω ε z)
  · intro z
    exact hGFF.gaussian.aemeasurable ⟨.circle ε z, hε, hdisks z z.property⟩
  · filter_upwards [hGFF.continuous_circle] with ω hcont
    exact hcont.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun z : U => ⟨hε, hdisks z z.property⟩)

/-- The jointly measurable version retains centered Gaussian marginals. -/
theorem IsDirichletGFF.exists_jointlyMeasurable_circle_gaussian
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {D U : Set ℂ}
    {h : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsDirichletGFF P D h hcirc) (ε : ℝ) (hε : 0 < ε)
    (hdisks : ∀ z ∈ U, Metric.closedBall z ε ⊆ D) :
    ∃ g : Ω × U → ℝ, Measurable g ∧
      (∀ᵐ ω ∂P, ∀ z : U, g (ω, z) = hcirc ω ε z) ∧
      ∀ z : U, ∃ v : ℝ≥0, HasLaw (fun ω => g (ω, z)) (gaussianReal 0 v) P := by
  obtain ⟨g, hg, heq⟩ := hGFF.exists_jointlyMeasurable_circle ε hε hdisks
  refine ⟨g, hg, heq, ?_⟩
  intro z
  let o : DirichletGFFObservable D := ⟨.circle ε z, hε, hdisks z z.property⟩
  have hgauss := hGFF.gaussian.hasGaussianLaw_eval o
  have hmean : (∫ ω, hcirc ω ε z ∂P) = 0 := hGFF.centered o.1 o.2
  refine ⟨(variance (fun ω => hcirc ω ε z) P).toNNReal, ?_⟩
  have hmap : P.map (fun ω => hcirc ω ε z) =
      gaussianReal 0 (variance (fun ω => hcirc ω ε z) P).toNNReal := by
    simpa [o, GFFObservable.eval, hmean] using hgauss.map_eq_gaussianReal
  exact ⟨(hg.comp (measurable_id.prodMk measurable_const)).aemeasurable,
    (Measure.map_congr (heq.mono fun ω hω => hω z)).trans hmap⟩

end MatedCRT

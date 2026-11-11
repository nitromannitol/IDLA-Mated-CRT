import MatedCRT.FirstPass.SLERef.Code
import MatedCRT.External.SLE

/-!
# Canonical whole-plane space-filling SLE model

This file gives a model of whole-plane space-filling SLE (Miller-Sheffield, *Imaginary Geometry IV*) in the sense of
`SpaceFillingSLEModel`, for a given family of laws `ν : ℝ → Measure SLEPathCode`.

The curve is read modulo increasing reparametrization, and the predicate `IsSLE` is read null-robustly: `𝓕 ≤ mΩ`, and
the law of the curve and its independence from `𝓕` are those of a measurable representative `ηL`, which is a.s. a
Lebesgue-area representative of the curve. Such a representative is parametrized by area and anchored at the spatial
point `0`, but its time change is only required to be an order isomorphism of `ℝ`.

For this model, monotonicity of independence (`SLEIndepMonoInput`) and closure under increasing reparametrization
(`SLEReparametrizationInput`) hold for every family `ν`. They are the per-model binders `hind` and `hrp` of the closed
theorems, so these binders are satisfiable for this model. The scale-invariance field `SLEScaleInvarianceInput`
(the binder `hsc`) is not proved here: for this model it needs a scale-invariance hypothesis on the family `ν`.
-/

namespace MatedCRT.ProbeMi
open MeasureTheory ProbabilityTheory Filter Topology

/-- Lebesgue-area representative without the time-0 anchoring `φ 0 = 0` (curve modulo reparametrization). -/
def IsLebesgueRepresentativeFree (η : ℝ → ℂ) (c : C(ℝ, ℂ)) : Prop :=
  c 0 = 0 ∧ Function.Surjective c ∧ Tendsto c (cocompact ℝ) (cocompact ℂ) ∧
  (∀ s t : ℝ, s ≤ t → volume (c '' Set.Icc s t) = ENNReal.ofReal (t - s)) ∧
  ∃ φ : ℝ ≃o ℝ, ∀ t : ℝ, η t = c (φ t)

/-- Canonical (null-robust) space-filling SLE model attached to a law family `ν`. -/
def canonicalSLEModel (ν : ℝ → Measure SLEPathCode) : SpaceFillingSLEModel where
  IsSLE := fun {Ω} mΩ P 𝓕 κ η =>
    IsProbabilityMeasure P ∧ 𝓕 ≤ mΩ ∧
    ∃ ηL : Ω → C(ℝ, ℂ), @Measurable Ω SLEPathCode mΩ _ (fun ω => slePathCode (ηL ω)) ∧
      (∀ᵐ ω ∂P, IsLebesgueRepresentativeFree (η ω) (ηL ω)) ∧
      @Measure.map Ω SLEPathCode mΩ _ (fun ω => slePathCode (ηL ω)) P = ν κ ∧
      Indep (MeasurableSpace.comap (fun ω => slePathCode (ηL ω)) inferInstance) 𝓕 P

/-- Monotonicity of independence (`SLEIndepMonoInput`) for the canonical model. The representative `ηL` is kept:
its code is independent of `𝓕`, hence of every sub-σ-algebra `𝓖 ≤ 𝓕`. -/
theorem canonicalSLEModel_indepMono (ν : ℝ → Measure SLEPathCode) :
    SLEIndepMonoInput (canonicalSLEModel ν) := by
  intro Ω mΩ P 𝓕 𝓖 κ η _ h h𝓖
  obtain ⟨hP, h𝓕, ηL, hm, hrep, hlaw, hind⟩ := h
  exact ⟨hP, h𝓖.trans h𝓕, ηL, hm, hrep, hlaw, indep_of_indep_of_le_right hind h𝓖⟩

/-- Closure under increasing reparametrization (`SLEReparametrizationInput`) for the canonical model. If `η'` is a.s.
`η ∘ φ` for an increasing homeomorphism `φ`, the same representative `ηL` serves for `η'`, its time change being
composed with `φ`; the law and independence clauses refer to `ηL` and are unchanged. -/
theorem canonicalSLEModel_reparam (ν : ℝ → Measure SLEPathCode) :
    SLEReparametrizationInput (canonicalSLEModel ν) := by
  intro Ω mΩ P 𝓕 κ η η' _ h hre
  obtain ⟨hP, h𝓕, ηL, hm, hrep, hlaw, hind⟩ := h
  refine ⟨hP, h𝓕, ηL, hm, ?_, hlaw, hind⟩
  filter_upwards [hrep, hre] with ω h1 h2
  obtain ⟨c0, csurj, cprop, cvol, φ, hφ⟩ := h1
  obtain ⟨ψ, hψmono, hψ⟩ := h2
  refine ⟨c0, csurj, cprop, cvol, (StrictMono.orderIsoOfSurjective ψ hψmono ψ.surjective).trans φ, ?_⟩
  intro t
  simp [hψ, hφ, StrictMono.orderIsoOfSurjective]
  rfl

end MatedCRT.ProbeMi

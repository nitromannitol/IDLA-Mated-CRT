import MatedCRT.FirstPass.Derived.AnnealedLawConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence of the annealed walk laws from the vertex of the origin

The annealed laws `annealedPathLaw S η' ε a` of the rescaled interpolated walks from a measurable starting vertex and
the origin mixture `originPathLaw ν` of a random path law are probability measures on `ContinuousPath ℂ`.  Under the
hypotheses of `tendsto_integral_annealedPathLaw`, the convergence against bounded Lipschitz path functionals (for the
uniform-on-compacts metric `dUnif`) is weak convergence of probability measures (portmanteau theorem).  A measurable
version `a_n` of the vertex `a^{ε_n}_0` of the origin always exists, so the starting vertices can be discharged.

* `measurable_annealedPathLawKernel`, `isProbabilityMeasure_annealedPathLaw`, `isProbabilityMeasure_originPathLaw`.
* `tendsto_annealedPathLaw_probabilityMeasure`: weak convergence along `ε_n → 0`.
* `exists_measurable_originVertex`: a measurable vertex field `a_n =ᵐ a^{ε_n}_0`.
* `exists_tendsto_annealedPathLaw_probabilityMeasure`: weak convergence from a measurable vertex field.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]
variable {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [PolishSpace Data] [BorelSpace Data]

/-- The quenched path law `ω ↦ Q^ε(a ω)(ω)` of the rescaled walk from a measurable vertex is measurable in `ω`. -/
theorem measurable_annealedPathLawKernel {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (ε : ℝ) {a : Ω → ℤ}
    (ha : Measurable a) :
    Measurable fun ω =>
      walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε (a ω) ω := by
  have hv : Measurable (fun ω => vertexPoint ε (⇑(η' ω))) := measurable_vertexPoint_curve hη' ε
  have hg : Measurable (fun p : Ω × ℤ =>
      walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε p.2 p.1) :=
    measurable_from_prod_countable_left fun k =>
      measurable_walkPathLaw hS hv (S.mε_nonneg ε) ε k
  exact hg.comp (measurable_id.prodMk ha)

/-- The annealed law of the rescaled walk from a measurable vertex is a probability measure. -/
theorem isProbabilityMeasure_annealedPathLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (ε : ℝ) {a : Ω → ℤ}
    (ha : Measurable a) :
    IsProbabilityMeasure (annealedPathLaw S η' ε a) := by
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact isProbabilityMeasure_bind
    (measurable_subtype_coe.comp (measurable_annealedPathLawKernel hS hη' ε ha)).aemeasurable
    (ae_of_all _ fun ω => (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε (a ω) ω).2)

omit [PolishSpace Data] in
/-- The origin mixture of a random path law is a probability measure. -/
theorem isProbabilityMeasure_originPathLaw
    (ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (originPathLaw ν) :=
  isProbabilityMeasure_bind measurable_originPathLawKernel.aemeasurable
    (ae_of_all _ fun p => (p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)).2)

omit [PolishSpace Data] in
/-- **Weak convergence of the annealed walk laws from the vertex of the origin.**  Under the hypotheses of
`tendsto_integral_annealedPathLaw`, the annealed laws of the rescaled walks from `a_n` converge weakly, as probability
measures on `ContinuousPath ℂ` with the topology of the metric `dUnif`, to the origin mixture `originPathLaw ν`. -/
theorem tendsto_annealedPathLaw_probabilityMeasure {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (e n) R δ ω} ≤ ENNReal.ofReal a)
    {a : ℕ → Ω → ℤ} (ha : ∀ n, Measurable (a n))
    (hav : ∀ n, ∀ᵐ ω ∂S.P, a n ω = vertexOf (e n) (S.η ω) 0)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))} [IsProbabilityMeasure ν]
    (hconv : ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D ω, interpWalkLaw S η' (e n) ω) ∂S.P) atTop (𝓝 (∫ p, f p ∂ν))) :
    Tendsto (β := ProbabilityMeasure (ContinuousPath ℂ)) (fun n => ⟨annealedPathLaw S η' (e n) (a n),
        isProbabilityMeasure_annealedPathLaw hS hη' (e n) (ha n)⟩)
      atTop (𝓝 ⟨originPathLaw ν, isProbabilityMeasure_originPathLaw ν⟩) := by
  refine tendsto_iff_forall_lipschitz_integral_tendsto.2 ?_
  intro f hfb hflip
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨K, hK⟩ := hflip
  exact tendsto_integral_annealedPathLaw hS hη' hae he0 he hmod ha hav hD hconv
    (BoundedContinuousFunction.mkOfBound ⟨f, hK.continuous⟩ C hC) hK

/-- **A measurable vertex field.**  Along `ε_n > 0` there are measurable `a_n : Ω → ℤ` with `a_n = a^{ε_n}_0`, the
vertex of the cell containing the origin, almost surely. -/
theorem exists_measurable_originVertex {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) :
    ∃ a : ℕ → Ω → ℤ, (∀ n, Measurable (a n)) ∧
      ∀ n, ∀ᵐ ω ∂S.P, a n ω = vertexOf (e n) (S.η ω) 0 := by
  choose V hV hVe using fun n => hS.exists_measurable_vertexOf (he0 n)
  exact ⟨fun n ω => V n (ω, 0), fun n => (hV n).comp (measurable_id.prodMk measurable_const),
    fun n => (hVe n).mono fun ω h => h 0⟩

omit [PolishSpace Data] in
/-- **Weak convergence of the annealed walk laws from a measurable vertex field of the origin.**  Under the
hypotheses of `tendsto_annealedPathLaw_probabilityMeasure` other than the starting vertices, there is a measurable
vertex field `a_n =ᵐ a^{ε_n}_0` along which the annealed laws converge weakly to `originPathLaw ν`. -/
theorem exists_tendsto_annealedPathLaw_probabilityMeasure {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (e n) R δ ω} ≤ ENNReal.ofReal a)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))} [IsProbabilityMeasure ν]
    (hconv : ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D ω, interpWalkLaw S η' (e n) ω) ∂S.P) atTop (𝓝 (∫ p, f p ∂ν))) :
    ∃ (a : ℕ → Ω → ℤ) (ha : ∀ n, Measurable (a n)),
      (∀ n, ∀ᵐ ω ∂S.P, a n ω = vertexOf (e n) (S.η ω) 0) ∧
      Tendsto (β := ProbabilityMeasure (ContinuousPath ℂ)) (fun n => ⟨annealedPathLaw S η' (e n) (a n),
          isProbabilityMeasure_annealedPathLaw hS hη' (e n) (ha n)⟩)
        atTop (𝓝 ⟨originPathLaw ν, isProbabilityMeasure_originPathLaw ν⟩) := by
  obtain ⟨a, ha, hav⟩ := exists_measurable_originVertex hS he0
  exact ⟨a, ha, hav, tendsto_annealedPathLaw_probabilityMeasure hS hη' hae he0 he hmod ha hav hD hconv⟩

end MatedCRT.FirstPass.Derived

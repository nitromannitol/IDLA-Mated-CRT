import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Bounded continuous tests of a random element converging in probability, jointly with a fixed coordinate

Let `A : Ω → X` be a random element and `Y^ε : Ω → Y` random elements converging in probability to `Y⁰` as
`ε → 0⁺`. Then the pairs `(A, Y^ε)` converge in law to `(A, Y⁰)`: for every bounded continuous
`f : X × Y → ℝ`, `E[f(A, Y^ε)] → E[f(A, Y⁰)]`. From any sequence `ε_n → 0⁺` extract a subsequence along which
`Y^ε → Y⁰` almost surely; along it `f(A, Y^ε) → f(A, Y⁰)` almost surely, and bounded convergence applies. This is
how the convergence in probability of the interpolated walk laws `P̃^ε` (Berestycki-Gwynne 2020, Theorem 1.2,
with the joint convergence with the field of Section 7.3) gives the convergence in law of `(R h, P̃^ε)` with an
unchanged first coordinate `R h`.

* `tendsto_integral_prodMk_of_exists_subseq_ae`: the statement for topological `X, Y`, with convergence in
  probability expressed as: every sequence `ε_n → 0⁺` has a subsequence along which `Y^ε → Y⁰` almost surely.
  For a pseudo-metrizable `Y` this is equivalent to convergence in probability for any compatible metric, and it
  needs no metric on `Y`.
* `tendsto_integral_prodMk_of_tendstoInMeasure`: the statement for a pseudo-(e)metric space `Y` and convergence
  in measure (`TendstoInMeasure`).
* `tendsto_integral_interpWalkLaw_of_exists_subseq_ae`: the case `Y = C(ℂ, Prob(ContinuousPath ℂ))` of the
  interpolated walk laws `P̃^ε` of a valid environment.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set
open MarkovProcess (ContinuousPath)
open scoped ENNReal NNReal BoundedContinuousFunction

/-- If every sequence `ε_n → 0⁺` has a subsequence along which `Y^ε → Y⁰` almost surely, then for every bounded
continuous `f`, `E[f(A, Y^ε)] → E[f(A, Y⁰)]` as `ε → 0⁺`. -/
theorem tendsto_integral_prodMk_of_exists_subseq_ae {Ω X Y : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] [TopologicalSpace X] [TopologicalSpace Y] {A : Ω → X}
    (hA : AEStronglyMeasurable A P) {Yε : ℝ → Ω → Y} {Y₀ : Ω → Y}
    (hY : ∀ ε, 0 < ε → AEStronglyMeasurable (Yε ε) P)
    (hsub : ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝[>] 0) → ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => Yε (e (ns n)) ω) atTop (𝓝 (Y₀ ω)))
    (f : X × Y →ᵇ ℝ) :
    Tendsto (fun ε => ∫ ω, f (A ω, Yε ε ω) ∂P) (𝓝[>] 0) (𝓝 (∫ ω, f (A ω, Y₀ ω) ∂P)) := by
  refine tendsto_of_subseq_tendsto fun e he => ?_
  obtain ⟨ns, hns, hae⟩ := hsub e he
  refine ⟨ns, ?_⟩
  have hpos : ∀ᶠ n in atTop, 0 < e (ns n) :=
    hns.tendsto_atTop.eventually (he.eventually eventually_mem_nhdsWithin)
  show Tendsto (fun n => ∫ ω, f (A ω, Yε (e (ns n)) ω) ∂P) atTop (𝓝 (∫ ω, f (A ω, Y₀ ω) ∂P))
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [hpos] with n hn
    exact f.continuous.comp_aestronglyMeasurable (hA.prodMk (hY _ hn))
  · exact Eventually.of_forall fun n => Eventually.of_forall fun ω => f.norm_coe_le_norm _
  · filter_upwards [hae] with ω hω
    exact (f.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hω)

/-- **Joint convergence with a fixed coordinate.** If `Y^ε → Y⁰` in probability as `ε → 0⁺`, then for every
bounded continuous `f`, `E[f(A, Y^ε)] → E[f(A, Y⁰)]`. -/
theorem tendsto_integral_prodMk_of_tendstoInMeasure {Ω X Y : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] [TopologicalSpace X] [PseudoEMetricSpace Y] {A : Ω → X}
    (hA : AEStronglyMeasurable A P) {Yε : ℝ → Ω → Y} {Y₀ : Ω → Y}
    (hY : ∀ ε, 0 < ε → AEStronglyMeasurable (Yε ε) P) (hconv : TendstoInMeasure P Yε (𝓝[>] 0) Y₀)
    (f : X × Y →ᵇ ℝ) :
    Tendsto (fun ε => ∫ ω, f (A ω, Yε ε ω) ∂P) (𝓝[>] 0) (𝓝 (∫ ω, f (A ω, Y₀ ω) ∂P)) :=
  tendsto_integral_prodMk_of_exists_subseq_ae hA hY
    (fun _ he => (hconv.comp he).exists_seq_tendsto_ae) f

/-- The case of the interpolated walk laws `P̃^ε` of a valid environment: if every sequence `ε_n → 0⁺` has a
subsequence along which `P̃^ε → Λ` almost surely in `C(ℂ, Prob(ContinuousPath ℂ))`, then for every bounded
continuous `f`, `E[f(A, P̃^ε)] → E[f(A, Λ)]` as `ε → 0⁺`. -/
theorem tendsto_integral_interpWalkLaw_of_exists_subseq_ae {X : Type*} [TopologicalSpace X]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {A : Ω → X} (hA : AEStronglyMeasurable A S.P) {Λ : Ω → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))}
    (hconv : ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝[>] 0) → ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂S.P, Tendsto (fun n => interpWalkLaw S η' (e (ns n)) ω) atTop (𝓝 (Λ ω)))
    (f : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ) :
    Tendsto (fun ε => ∫ ω, f (A ω, interpWalkLaw S η' ε ω) ∂S.P) (𝓝[>] 0)
      (𝓝 (∫ ω, f (A ω, Λ ω) ∂S.P)) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact tendsto_integral_prodMk_of_exists_subseq_ae hA
    (fun _ hε => (aemeasurable_interpWalkLaw hS hη' hae hε).aestronglyMeasurable) hconv f

end MatedCRT

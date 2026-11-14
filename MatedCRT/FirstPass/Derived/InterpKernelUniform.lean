import MatedCRT.FirstPass.Derived.InterpKernelModulus
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import LatticeProb.Prob.LawKernelTightness
import LatticeProb.Prob.PathSpaceDUnif

/-!
# The kernel modulus of the interpolated walk laws, uniformly in the mesh index

The interpolated quenched walk law `P̃^ε(ω) : ℂ → Prob(ContinuousPath ℂ)` is transported to the
Lévy–Prokhorov side by the homeomorphism `Prob X ≃ₜ LevyProkhorov (Prob X)`
(`interpWalkLawLP`, with the uniform-on-compacts metric `dUnif` on `ContinuousPath ℂ`).  The
modulus failure event of `LatticeProb.kernelModulusFailure` for `interpWalkLawLP` is the event of
`exists_delta_eventually_interpWalkLaw_modulus` (`mem_kernelModulusFailure_interpWalkLawLP_iff`),
so the passage from large `n` to all `n` (`LatticeProb.exists_delta_forall_of_eventually`) gives a
scale `δ` that works for every mesh size.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- The interpolated quenched walk law with values in the Lévy–Prokhorov space of probability
measures on `ContinuousPath ℂ`. -/
noncomputable def interpWalkLawLP (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε : ℝ) (ω : Ω) :
    C(ℂ, LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))) :=
  ContinuousMap.comp
    ⟨LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ),
      (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ)).continuous⟩
    (interpWalkLaw S η' ε ω)

/-- The modulus failure of the transported kernel is the event of the Lévy–Prokhorov distance of the
laws at two nearby points being large. -/
theorem mem_kernelModulusFailure_interpWalkLawLP_iff (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ))
    (ε : ℝ) (ω : Ω) (L δ : ℝ) :
    interpWalkLawLP S η' ε ω ∈ kernelModulusFailure (0 : ℂ) L δ ↔
      ∃ z w : ℂ, dist z 0 ≤ L ∧ dist w 0 ≤ L ∧ dist z w ≤ δ ∧
        1 / L < (pathLevyProkhorovEDist (interpWalkLaw S η' ε ω z)
          (interpWalkLaw S η' ε ω w)).toReal :=
  Iff.rfl

/-- The transported interpolated walk law is almost everywhere measurable. -/
theorem aemeasurable_interpWalkLawLP {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℝ} (hε : 0 < ε) :
    AEMeasurable (interpWalkLawLP S η' ε) S.P :=
  (ContinuousMap.continuous_postcomp
    (⟨LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ),
      (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ)).continuous⟩ :
      C(ProbabilityMeasure (ContinuousPath ℂ),
        LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))))).measurable.comp_aemeasurable
    (aemeasurable_interpWalkLaw hS hη' hae hε)

/-- **The modulus of continuity in law of the interpolated walk, uniformly in `n`.**  If the
vertex-indexed modulus of the quenched walk laws is small with high probability for large `n`
(`hEq`), then for every `L > 1` there is one scale `δ > 0` such that, for **every** `n`, with
probability at least `1 - 1/L` the laws `P̃^{ε_n}_z`, `P̃^{ε_n}_w` with `|z|, |w| ≤ L`,
`|z - w| ≤ δ` are at Lévy–Prokhorov distance at most `1/L`. -/
theorem exists_delta_forall_interpWalkLaw_modulus {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n)
    (hε : Tendsto eps atTop (𝓝 0))
    (hEq : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a)
    {L : ℝ} (hL : 1 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      S.P {ω | ∃ z w : ℂ, dist z 0 ≤ L ∧ dist w 0 ≤ L ∧ dist z w ≤ δ ∧
        1 / L < (pathLevyProkhorovEDist (interpWalkLaw S η' (eps n) ω z)
          (interpWalkLaw S η' (eps n) ω w)).toReal} ≤ ENNReal.ofReal (1 / L) := by
  have hLpos : 0 < L := by linarith
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨δ0, hδ0, hev⟩ := exists_delta_eventually_interpWalkLaw_modulus hS hae hε0 hε hEq hL
  obtain ⟨δ, hδ, hall⟩ := exists_delta_forall_of_eventually (fun _ : ℕ => S.P)
    (fun n ω => interpWalkLawLP S η' (eps n) ω) (0 : ℂ) hLpos
    (fun n δ => (aemeasurable_interpWalkLawLP hS hη' hae (hε0 n)).nullMeasurable
      (isOpen_kernelModulusFailure (0 : ℂ) L δ).measurableSet)
    ⟨δ0, hδ0, hev.mono fun n hn => by
      simp only [mem_kernelModulusFailure_interpWalkLawLP_iff]
      exact hn⟩
  refine ⟨δ, hδ, fun n => ?_⟩
  have h := hall n
  simp only [mem_kernelModulusFailure_interpWalkLawLP_iff] at h
  exact h

end MatedCRT.FirstPass.Derived

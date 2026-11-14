import MatedCRT.FirstPass.Derived.InterpKernelTight
import LatticeProb.Prob.TightnessProduct
import LatticeProb.Prob.TightnessPushforward

/-!
# Joint tightness of a Polish datum and the interpolated quenched walk laws

For a mesh sequence `ε_n → 0` and a random element `D` of a Polish space (the environment datum),
the laws of the pairs `(D, P̃^{ε_n})` form a tight set in `Data × C(ℂ, 𝒫(ContinuousPath ℂ))`:
tightness of the interpolated walk laws (`isTightMeasureSet_interpWalkLawLP`, transported from the
Lévy–Prokhorov space by the inverse homeomorphism) and tightness of the single law of `D`, combined
by `LatticeProb.isTightMeasureSet_map_pair`.  All random elements are only almost everywhere
measurable; laws are unchanged by modifying them on null sets.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] dUnifMetricSpace

section AE

variable {A ι W : Type*} [MeasurableSpace W] [MeasurableSpace A]

/-- Laws of almost everywhere equal random elements coincide, so tightness transfers. -/
theorem isTightMeasureSet_of_ae_eq [TopologicalSpace A] (μ : ι → Measure W) (X X' : ι → W → A)
    (h : ∀ i, X i =ᵐ[μ i] X' i)
    (hX' : IsTightMeasureSet {ν : Measure A | ∃ i, ν = (μ i).map (X' i)}) :
    IsTightMeasureSet {ν : Measure A | ∃ i, ν = (μ i).map (X i)} := by
  have hset : {ν : Measure A | ∃ i, ν = (μ i).map (X i)} =
      {ν : Measure A | ∃ i, ν = (μ i).map (X' i)} := by
    ext ν
    simp only [mem_ofPred_eq]
    exact exists_congr fun i => by rw [Measure.map_congr (h i)]
  rw [hset]
  exact hX'

end AE

/-- Postcomposition with the inverse of the homeomorphism `𝒫(E) ≃ₜ LévyProkhorov 𝒫(E)`: the
continuous map `C(ℂ, LévyProkhorov 𝒫(E)) → C(ℂ, 𝒫(E))` that forgets the metric structure. -/
noncomputable def levyProkhorovUnwrap :
    C(ℂ, LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))) →
      C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) := fun f =>
  ContinuousMap.comp
    ⟨(LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ)).symm,
      (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ)).symm.continuous⟩ f

theorem continuous_levyProkhorovUnwrap : Continuous levyProkhorovUnwrap :=
  ContinuousMap.continuous_postcomp
    (⟨(LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ)).symm,
      (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ)).symm.continuous⟩ :
      C(LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ)),
        ProbabilityMeasure (ContinuousPath ℂ)))

variable {Ω : Type} [MeasurableSpace Ω]

theorem levyProkhorovUnwrap_interpWalkLawLP (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε : ℝ)
    (ω : Ω) : levyProkhorovUnwrap (interpWalkLawLP S η' ε ω) = interpWalkLaw S η' ε ω :=
  ContinuousMap.ext fun z =>
    (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ContinuousPath ℂ)).symm_apply_apply _

/-- **Joint tightness of a Polish datum and the interpolated quenched walk laws.** -/
theorem isTightMeasureSet_data_interpWalkLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n)
    (hε : Tendsto eps atTop (𝓝 0))
    (hEq : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a)
    (hEqPath : ∀ R L a : ℝ, 0 < L → 0 < a → ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ᶠ n in atTop, S.P (vertexPathFailure S η' (eps n) R L a δ) ≤ ENNReal.ofReal a)
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [PolishSpace Data]
    [BorelSpace Data] (D : Ω → Data) (hD : AEMeasurable D S.P) :
    IsTightMeasureSet {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) |
      ∃ n, ν = S.P.map fun ω => (D ω, interpWalkLaw S η' (eps n) ω)} := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hY := isTightMeasureSet_interpWalkLawLP hS hη' hae hε0 hε hEq hEqPath
  have hYae : ∀ n, AEMeasurable (interpWalkLawLP S η' (eps n)) S.P := fun n =>
    aemeasurable_interpWalkLawLP hS hη' hae (hε0 n)
  -- measurable modifications
  set Y' : ℕ → Ω → C(ℂ, LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))) :=
    fun n => (hYae n).mk _ with hY'
  have hY'm : ∀ n, Measurable (Y' n) := fun n => (hYae n).measurable_mk
  have hY'ae : ∀ n, interpWalkLawLP S η' (eps n) =ᵐ[S.P] Y' n := fun n => (hYae n).ae_eq_mk
  have hYt' : IsTightMeasureSet {ν : Measure
      C(ℂ, LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))) |
      ∃ n, ν = S.P.map (Y' n)} :=
    isTightMeasureSet_of_ae_eq (fun _ : ℕ => S.P) Y' (interpWalkLawLP S η' ∘ eps)
      (fun n => (hY'ae n).symm) hY
  have hZt : IsTightMeasureSet {ν : Measure C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) |
      ∃ n, ν = S.P.map fun ω => levyProkhorovUnwrap (Y' n ω)} :=
    isTightMeasureSet_map_comp (fun _ : ℕ => S.P) Y' hY'm hYt' continuous_levyProkhorovUnwrap
      continuous_levyProkhorovUnwrap.measurable
  have hD'm : Measurable (hD.mk D) := hD.measurable_mk
  have hDt : IsTightMeasureSet {ν : Measure Data | ∃ _ : ℕ, ν = S.P.map (hD.mk D)} := by
    refine (isTightMeasureSet_singleton_of_innerRegular (μ := S.P.map (hD.mk D))).subset ?_
    rintro _ ⟨_, rfl⟩
    exact mem_singleton _
  have hpair := isTightMeasureSet_map_pair (fun _ : ℕ => S.P) (fun _ => hD.mk D)
    (fun n ω => levyProkhorovUnwrap (Y' n ω)) (fun _ => hD'm)
    (fun n => continuous_levyProkhorovUnwrap.measurable.comp (hY'm n)) hDt hZt
  refine isTightMeasureSet_of_ae_eq (fun _ : ℕ => S.P)
    (fun n ω => (D ω, interpWalkLaw S η' (eps n) ω))
    (fun n ω => (hD.mk D ω, levyProkhorovUnwrap (Y' n ω))) (fun n => ?_) hpair
  filter_upwards [hD.ae_eq_mk, hY'ae n] with ω h1 h2
  refine Prod.ext h1 ?_
  show interpWalkLaw S η' (eps n) ω = levyProkhorovUnwrap (Y' n ω)
  rw [← h2]
  exact (levyProkhorovUnwrap_interpWalkLawLP S η' (eps n) ω).symm

end MatedCRT.FirstPass.Derived

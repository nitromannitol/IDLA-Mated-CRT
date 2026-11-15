import MatedCRT.FirstPass.Derived.ConeFieldSigmaCurveIndep
import MatedCRT.FirstPass.Derived.ValidEnvironmentLaw
import MatedCRT.FirstPass.SLERef.CanonicalModel

/-! # Canonical SLE model for a matching mating-of-trees coupling -/

noncomputable section

open MeasureTheory ProbabilityTheory Set HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- A matching coupling supplies the canonical model's SLE predicate when its
Lebesgue-parametrized curve has the specified code law. -/
theorem canonicalSLEModel_isSLE_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ : ℝ}
    {ν : ℝ → Measure SLEPathCode}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hcone : IsQuantumCone γ S.P S.hC S.hcirc)
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ)
    (hlaw : S.P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    (ProbeMi.canonicalSLEModel ν).IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η := by
  have hfield : S.fieldSigma ≤ (inferInstance : MeasurableSpace Ω) := by
    refine iSup₂_le fun φ hφ => ?_
    exact ((hcone.measurable_pairing φ hφ).sub_const _).comap_le
  have hi := indep_fieldSigma_igCurve_of_coupling hγ hγ2 D hrep
  have hcode : MeasurableSpace.comap (fun ω => slePathCode (ηL ω)) inferInstance ≤
      MeasurableSpace.comap ηL inferInstance := by
    change MeasurableSpace.comap (slePathCode ∘ ηL) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono measurableEmbedding_slePathCode.measurable.comap_le
  have hrepr := ae_isLebesgueRepresentative_of_coupling D hη
  refine ⟨D.isProbabilityMeasure, hfield, ηL,
    measurableEmbedding_slePathCode.measurable.comp D.measurable_curves.1, ?_, hlaw,
    (indep_of_indep_of_le_right hi hcode).symm⟩
  filter_upwards [hrepr] with ω hω
  obtain ⟨h0, hsurj, hproper, hvol, φ, _, hφ⟩ := hω
  exact ⟨h0, hsurj, hproper, hvol, φ, hφ⟩

end MatedCRT.FirstPass.Derived

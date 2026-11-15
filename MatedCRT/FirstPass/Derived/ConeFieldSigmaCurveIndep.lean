import MatedCRT.FirstPass.Derived.ConeDistributionAreaIndep
import HarmonicBalls.Steps.Sec11.LocalPairingLaw

/-! # Independence of the cone field and the Lebesgue curve -/

noncomputable section

open MeasureTheory ProbabilityTheory Set HarmonicBalls
open scoped NNReal

namespace MatedCRT

/-- Matching all test pairings on one event makes the field sigma algebra
independent of the Lebesgue-parametrized curve in the same coupling. -/
theorem indep_fieldSigma_igCurve_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    Indep S.fieldSigma (MeasurableSpace.comap ηL inferInstance) S.P := by
  obtain ⟨H, _, hind, hH⟩ :=
    FirstPass.Derived.exists_coneField_version_indepFun_igCurve h hγ hγ2
  have heq : (pairingCodeOf ∘ H) =ᵐ[S.P] fieldPairingCode S := by
    filter_upwards [hrep, hH] with ω hr hh
    funext φ
    change H ω (MatedCRT.Field.toTestC φ.2) = S.hC ω φ.1
    exact ((hr (MatedCRT.Field.toTestC φ.2)).trans
      (congrArg (fun F : LQGMetric.DistC => F (MatedCRT.Field.toTestC φ.2)) hh)).symm
  have hi : IndepFun (fieldPairingCode S) ηL S.P :=
    (hind.comp measurable_pairingCodeOf measurable_id).congr heq (Filter.EventuallyEq.rfl)
  have hs : S.fieldSigma = MeasurableSpace.comap (fieldPairingCode S) inferInstance := by
    rw [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra_eq_comap_localFieldPairings]
    congr 1
    funext ω φ
    simp only [localFieldPairings, fieldPairingCode, fieldPairing, zero_mul, sub_zero]
  rw [hs]
  exact hi

end MatedCRT

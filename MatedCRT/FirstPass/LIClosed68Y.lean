import MatedCRT.FirstPass.S4S6c.Closed6x68Y
import MatedCRT.FirstPass.S4S6c.VolCutoffField68
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCYSqHalf68

/-!
# Volume cutoff of the Y route from Berestycki--Gwynne

The named input `Lemma68CGRCY.FieldVolCutoffStmt` of `firstPass_6_7/8/9_of_hOneY` (Closed6x68Y.lean) is discharged from the
frozen Berestycki--Gwynne ball-mass input `FrozenBerestyckiGwynneConeBallMass` through Lemma 2.7
(`volumeGrowthStmt_of_berestyckiGwynne`, ConeBallMass.lean:17) and the field-measurable cutoff
(`VolCutoffField68.volume_lower_cutoff_fieldMeasurable_vr`, VolCutoffField68.lean:171). The remaining non-frozen input is
the one-test producer `hOneY : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮`.
-/

open MeasureTheory

namespace MatedCRT
namespace LIClosed68Y

/-- **Field-measurable volume cutoff from Berestycki--Gwynne.** -/
theorem fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 : SpaceFillingSLEModel)
    (hBG : FrozenBerestyckiGwynneConeBallMass) : Lemma68CGRCY.FieldVolCutoffStmt 𝒮 := by
  have hVG : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  intro γ hγ hγ2 Ω _ S hS
  exact VolCutoffField68.volume_lower_cutoff_fieldMeasurable_vr hγ hγ2 hVG S hS

/-- **Lemma 6.7, first pass.** `Lemma68CGRCYSqHalf.firstPass_6_7_sq` with the volume
growth input from the frozen Berestycki--Gwynne ball mass (Lemma 2.7, `volumeGrowthStmt_of_berestyckiGwynne`). -/
theorem firstPass_6_7 {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68CGRCYSqHalf.firstPass_6_7_sq hCRM hLit hBM hCC hB1 hμ (volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- **Lemma 6.8, first pass.** `Lemma68CGRCYSqHalf.firstPass_6_8_sq`. -/
theorem firstPass_6_8 {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  Lemma68CGRCYSqHalf.firstPass_6_8_sq hCRM hLit hBM hCC hB1 hμ hBG

/-- **Lemma 6.9, first pass.** `Lemma68CGRCYSqHalf.firstPass_6_9_sq` with the volume
growth input from the frozen Berestycki--Gwynne ball mass. -/
theorem firstPass_6_9 {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  Lemma68CGRCYSqHalf.firstPass_6_9_sq hCRM hLit hBM hCC hB1 hμ (volumeGrowthStmt_of_berestyckiGwynne hBG)

end LIClosed68Y
end MatedCRT

#print axioms MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne
#print axioms MatedCRT.LIClosed68Y.firstPass_6_7
#print axioms MatedCRT.LIClosed68Y.firstPass_6_8
#print axioms MatedCRT.LIClosed68Y.firstPass_6_9

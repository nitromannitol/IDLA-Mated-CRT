import MatedCRT.FirstPass.S4S6c.Closed6x68Y
import MatedCRT.FirstPass.S4S6c.VolCutoffField68
import MatedCRT.Proofs.Sec3.ConeBallMass

/-!
# Lead glue (lead li): volume cutoff of the Y route from Berestycki--Gwynne

The named input `Lemma68CGRCY.FieldVolCutoffStmt` of `firstPass_6_7/8/9_of_hOneY` (Closed6x68Y.lean) is discharged from the
frozen Berestycki--Gwynne ball-mass input `FrozenBerestyckiGwynneConeBallMass` through Lemma 2.7
(`volumeGrowthStmt_of_berestyckiGwynne`, ConeBallMass.lean:17) and q2's field-measurable cutoff
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

end LIClosed68Y
end MatedCRT

#print axioms MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne

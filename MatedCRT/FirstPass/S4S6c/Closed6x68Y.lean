import MatedCRT.FirstPass.S4S6c.Closed6x68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCY68
import MatedCRT.FirstPass.S4S6c.VolCutoffField68

/-!
# First-pass forms of Lemmas 6.7, 6.8, 6.9 from the Y counting CG one-test input (fp-S4S6c-chain-y, lead li 20:05 UTC)

Analogues of `firstPass_6_7/8/9_of_hOneX` (Closed6x68X.lean:74-114) with the one-test producer
`LICGRCY68.ShellOneTestOrderAeCGRCYStmt` (`hOneY`). The conclusions are those of the X forms.

The field-measurable volume cutoff `FieldVolCutoffStmt 𝒮` (ShellChainCGRCY68.lean) is no longer a binder: it is
derived from `VolumeGrowthStmt` by `fieldVolCutoffStmt_of_volumeGrowth` (q2's
`VolCutoffField68.volume_lower_cutoff_fieldMeasurable_vr`, VolCutoffField68.lean:171).

* Lemma 6.8: `VolumeGrowthStmt` is `volumeGrowthStmt_of_berestyckiGwynne hBG`, so the binders are exactly those of
  `firstPass_6_8_of_hOneX` with `hOneX` replaced by `hOneY`.
* Lemmas 6.7 and 6.9: the X forms have no volume-growth input (their chain uses only `hLit`..`hμ` through
  `ShortWindowHV.hprev_of_shortWindow_noH0V`). The Y chain needs `VolumeGrowthStmt` for the random cutoff, so the
  binder `hVG : VolumeGrowthStmt` is added. This is the only binder change (report to lead).

No `C ≤ CG` premise anywhere (Codex Q4). The Green exponent `ωG` comes from `CountingMeshEventsHiStmt`
(`countingMeshEventsHi_of_draft`).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRT

/-- **Field-measurable volume cutoff from volume growth (q2, VolCutoffField68.lean:171).** Discharges the named input
`Lemma68CGRCY.FieldVolCutoffStmt 𝒮` of the Y chain. -/
theorem fieldVolCutoffStmt_of_volumeGrowth {𝒮 : SpaceFillingSLEModel} (hVG : VolumeGrowthStmt) :
    Lemma68CGRCY.FieldVolCutoffStmt 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS
  exact VolCutoffField68.volume_lower_cutoff_fieldMeasurable_vr hγ hγ2 hVG S hS

/-- **Lemma 6.7, first-pass form of the Y counting CG route.** As `firstPass_6_7_of_hOneX` with `hOneY`, and the
volume growth input `hVG` (the random cutoff of the Y chain). -/
theorem firstPass_6_7_of_hOneY {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVG : VolumeGrowthStmt)
    (hOneY : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTopCGRCY.hU_top_cgRCY (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ (fieldVolCutoffStmt_of_volumeGrowth hVG) hOneY)

/-- **Lemma 6.8, first-pass form of the Y counting CG route.** As `firstPass_6_8_of_hOneX` with `hOneY`; the volume
growth is `volumeGrowthStmt_of_berestyckiGwynne hBG`, so no extra binder. -/
theorem firstPass_6_8_of_hOneY {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hOneY : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTopCGRCY.hU_top_cgRCY (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ (fieldVolCutoffStmt_of_volumeGrowth (volumeGrowthStmt_of_berestyckiGwynne hBG)) hOneY)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) (CertifiedReferenceModel.cellSizeEstimate hCRM)

/-- **Lemma 6.9, first-pass form of the Y counting CG route.** As `firstPass_6_9_of_hOneX` with `hOneY`, and the
volume growth input `hVG`. -/
theorem firstPass_6_9_of_hOneY {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVG : VolumeGrowthStmt)
    (hOneY : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTopCGRCY.hU_top_cgRCY (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ (fieldVolCutoffStmt_of_volumeGrowth hVG) hOneY)

end MatedCRT

#print axioms MatedCRT.firstPass_6_7_of_hOneY
#print axioms MatedCRT.firstPass_6_8_of_hOneY
#print axioms MatedCRT.firstPass_6_9_of_hOneY
